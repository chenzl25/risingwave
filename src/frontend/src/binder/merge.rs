// Copyright 2022 RisingWave Labs
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::collections::HashSet;
use std::ops::Range;

use risingwave_common::catalog::TableVersionId;
use risingwave_sqlparser::ast::{
    Expr, Ident, MergeAction, MergeClause, MergeClauseKind, ObjectName, TableAlias, TableFactor,
};

use super::statement::RewriteExprsRecursive;
use crate::binder::{Binder, BoundBaseTable, Relation};
use crate::catalog::TableId;
use crate::error::{ErrorCode, Result, bail_bind_error};
use crate::expr::ExprImpl;

#[derive(Debug, Clone)]
pub struct BoundMerge {
    pub target: BoundBaseTable,
    pub source: Relation,
    pub on: ExprImpl,
    pub clauses: Vec<BoundMergeClause>,
    pub row_identity: BoundMergeRowIdentity,
}

#[derive(Debug, Clone)]
pub struct BoundMergeRowIdentity {
    pub candidate_target_range: Range<usize>,
    pub candidate_source_range: Range<usize>,
    /// Authoritative identity contract for the target side.
    /// All column indices below are base-table column indices from `target.table_catalog`.
    pub target_table_id: TableId,
    pub target_table_version_id: TableVersionId,
    pub target_pk_column_indices: Vec<usize>,
    pub source_identity: BoundMergeSourceIdentity,
}

#[derive(Debug, Clone)]
pub struct BoundMergeSourceIdentity {
    pub candidate_source_range: Range<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundMergeClauseKind {
    Matched,
    NotMatched,
}

#[derive(Debug, Clone)]
pub struct BoundMergeClause {
    pub kind: BoundMergeClauseKind,
    pub condition: Option<ExprImpl>,
    pub action: BoundMergeAction,
}

#[derive(Debug, Clone)]
pub enum BoundMergeAction {
    Update {
        assignments: Vec<BoundMergeAssignment>,
    },
    Delete,
    Insert {
        target_table_column_indices: Vec<usize>,
        values: Vec<ExprImpl>,
    },
}

#[derive(Debug, Clone)]
pub struct BoundMergeAssignment {
    /// Base-table column index in `target.table_catalog`.
    pub target_table_column_index: usize,
    pub expr: ExprImpl,
}

impl RewriteExprsRecursive for BoundMerge {
    fn rewrite_exprs_recursive(&mut self, rewriter: &mut impl crate::expr::ExprRewriter) {
        self.source.rewrite_exprs_recursive(rewriter);
        self.on = rewriter.rewrite_expr(self.on.take());
        for clause in &mut self.clauses {
            clause.rewrite_exprs_recursive(rewriter);
        }
    }
}

impl RewriteExprsRecursive for BoundMergeClause {
    fn rewrite_exprs_recursive(&mut self, rewriter: &mut impl crate::expr::ExprRewriter) {
        self.condition =
            std::mem::take(&mut self.condition).map(|expr| rewriter.rewrite_expr(expr));
        self.action.rewrite_exprs_recursive(rewriter);
    }
}

impl RewriteExprsRecursive for BoundMergeAction {
    fn rewrite_exprs_recursive(&mut self, rewriter: &mut impl crate::expr::ExprRewriter) {
        match self {
            BoundMergeAction::Update { assignments } => {
                for assignment in assignments {
                    assignment.expr = rewriter.rewrite_expr(assignment.expr.take());
                }
            }
            BoundMergeAction::Delete => {}
            BoundMergeAction::Insert { values, .. } => {
                for value in values {
                    *value = rewriter.rewrite_expr(value.take());
                }
            }
        }
    }
}

impl Binder {
    pub(super) fn bind_merge(
        &mut self,
        table_name: ObjectName,
        table_alias: Option<TableAlias>,
        source: TableFactor,
        on: Expr,
        clauses: Vec<MergeClause>,
    ) -> Result<BoundMerge> {
        let target_relation =
            self.bind_relation_by_name(&table_name, table_alias.as_ref(), None, false)?;
        let Relation::BaseTable(target) = target_relation else {
            bail_bind_error!("MERGE target must be a base table");
        };
        let target = *target;
        let target_range = 0..self.context.columns.len();

        let target_table_id = target.table_id;
        let target_table_version_id = target
            .table_catalog
            .version_id()
            .expect("table must be versioned");
        let target_table_name = target.table_catalog.name().to_owned();

        let source = self.bind_table_factor(&source)?;
        let source_range = target_range.end..self.context.columns.len();

        let on = self.bind_expr(&on)?.enforce_bool_clause("MERGE ON")?;
        let bound_clauses = clauses
            .into_iter()
            .map(|clause| {
                self.bind_merge_clause(
                    clause,
                    &target,
                    table_alias.as_ref(),
                    &target_table_name,
                    &target_range,
                )
            })
            .collect::<Result<Vec<_>>>()?;

        let row_identity = BoundMergeRowIdentity {
            candidate_target_range: target_range.clone(),
            candidate_source_range: source_range.clone(),
            target_table_id,
            target_table_version_id,
            target_pk_column_indices: target
                .table_catalog
                .pk()
                .iter()
                .map(|pk| pk.column_index)
                .collect(),
            source_identity: BoundMergeSourceIdentity {
                candidate_source_range: source_range,
            },
        };

        Ok(BoundMerge {
            target,
            source,
            on,
            clauses: bound_clauses,
            row_identity,
        })
    }

    fn bind_merge_clause(
        &mut self,
        clause: MergeClause,
        target: &BoundBaseTable,
        target_alias: Option<&TableAlias>,
        target_table_name: &str,
        target_range: &Range<usize>,
    ) -> Result<BoundMergeClause> {
        let kind = match clause.kind {
            MergeClauseKind::Matched => BoundMergeClauseKind::Matched,
            MergeClauseKind::NotMatched => BoundMergeClauseKind::NotMatched,
        };
        let condition = clause
            .condition
            .map(|expr| self.bind_expr(&expr)?.enforce_bool_clause("MERGE WHEN"))
            .transpose()?;
        let action = self.bind_merge_action(
            clause.action,
            target,
            target_alias,
            target_table_name,
            target_range,
        )?;
        Ok(BoundMergeClause {
            kind,
            condition,
            action,
        })
    }

    fn bind_merge_action(
        &mut self,
        action: MergeAction,
        target: &BoundBaseTable,
        target_alias: Option<&TableAlias>,
        target_table_name: &str,
        target_range: &Range<usize>,
    ) -> Result<BoundMergeAction> {
        match action {
            MergeAction::Update { assignments } => {
                let assignments = assignments
                    .into_iter()
                    .map(|assignment| {
                        let target_index = resolve_merge_target_index(
                            target,
                            target_alias,
                            target_table_name,
                            target_range,
                            &assignment.id,
                        )?;
                        let expr = match assignment.value {
                            risingwave_sqlparser::ast::AssignmentValue::Expr(expr) => {
                                self.bind_expr(&expr)?
                            }
                            risingwave_sqlparser::ast::AssignmentValue::Default => {
                                bail_bind_error!("MERGE UPDATE SET DEFAULT is not supported yet")
                            }
                        };
                        Ok(BoundMergeAssignment {
                            target_table_column_index: target_index,
                            expr,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(BoundMergeAction::Update { assignments })
            }
            MergeAction::Delete => Ok(BoundMergeAction::Delete),
            MergeAction::Insert { columns, values } => {
                let column_indices = resolve_merge_insert_columns(
                    target,
                    target_alias,
                    target_table_name,
                    target_range,
                    columns,
                )?;
                if column_indices.len() != values.len() {
                    return Err(ErrorCode::BindError(format!(
                        "MERGE INSERT has {} target columns but {} values",
                        column_indices.len(),
                        values.len()
                    ))
                    .into());
                }
                let values = values
                    .into_iter()
                    .map(|expr| self.bind_expr(&expr))
                    .collect::<Result<Vec<_>>>()?;
                Ok(BoundMergeAction::Insert {
                    target_table_column_indices: column_indices,
                    values,
                })
            }
        }
    }
}

fn resolve_merge_insert_columns(
    target: &BoundBaseTable,
    target_alias: Option<&TableAlias>,
    target_table_name: &str,
    target_range: &Range<usize>,
    columns: Vec<Ident>,
) -> Result<Vec<usize>> {
    if columns.is_empty() {
        return Ok(target
            .table_catalog
            .columns()
            .iter()
            .enumerate()
            .filter(|(_, column)| !column.is_hidden())
            .map(|(idx, _)| target_range.start + idx)
            .collect());
    }

    let mut seen = HashSet::new();
    let mut column_indices = Vec::with_capacity(columns.len());
    for column in columns {
        let idx = resolve_merge_target_index(
            target,
            target_alias,
            target_table_name,
            target_range,
            &[column],
        )?;
        if !seen.insert(idx) {
            bail_bind_error!("column specified more than once in MERGE INSERT");
        }
        column_indices.push(idx);
    }
    Ok(column_indices)
}

fn resolve_merge_target_index(
    target: &BoundBaseTable,
    target_alias: Option<&TableAlias>,
    target_table_name: &str,
    target_range: &Range<usize>,
    id: &[Ident],
) -> Result<usize> {
    let column_name = match id {
        [column] => column.real_value(),
        [qualifier, column] => {
            let qualifier = qualifier.real_value();
            let expected_qualifier = target_alias
                .map(|alias| alias.name.real_value())
                .unwrap_or_else(|| target_table_name.to_owned());
            if qualifier != expected_qualifier {
                bail_bind_error!(
                    "MERGE target column qualifier must refer to the target table or alias"
                );
            }
            column.real_value()
        }
        _ => bail_bind_error!("invalid MERGE target column reference"),
    };

    target
        .table_catalog
        .columns()
        .iter()
        .enumerate()
        .find(|(_, column)| column.name() == column_name)
        .map(|(idx, _)| target_range.start + idx)
        .ok_or_else(|| {
            ErrorCode::ItemNotFound(format!(
                "column \"{}\" of relation \"{}\"",
                column_name, target_table_name
            ))
            .into()
        })
}

#[cfg(test)]
mod tests {
    use risingwave_sqlparser::test_utils::parse_sql_statements;

    use super::{BoundMergeAction, BoundMergeClauseKind};
    use crate::FrontendOpts;
    use crate::binder::{Binder, BoundStatement};
    use crate::test_utils::LocalFrontend;

    #[tokio::test]
    async fn bind_merge_preserves_clause_order_and_identity_contract() {
        let frontend = LocalFrontend::new(FrontendOpts::default()).await;
        frontend
            .run_sql("create table target (id int primary key, v int);")
            .await
            .unwrap();
        frontend
            .run_sql("create table source (id int primary key, v int);")
            .await
            .unwrap();

        let session = frontend.session_ref();
        let mut binder = Binder::new_for_batch(&session);
        let stmt = parse_sql_statements(
            "merge into target as t using source as s on t.id = s.id \
             when matched and s.v > 10 then update set v = s.v \
             when not matched and s.v > 0 then insert (id, v) values (s.id, s.v)",
        )
        .unwrap()
        .remove(0);

        let bound = binder.bind(stmt).unwrap();
        let BoundStatement::Merge(merge) = bound else {
            panic!("expected BoundStatement::Merge");
        };

        let target_len = merge.target.table_catalog.columns().len();
        assert_eq!(merge.row_identity.candidate_target_range, 0..target_len);
        assert_eq!(
            merge.row_identity.candidate_source_range.start,
            merge.row_identity.candidate_target_range.end
        );
        assert_eq!(
            merge.row_identity.target_pk_column_indices,
            merge.target
                .table_catalog
                .pk()
                .iter()
                .map(|pk| pk.column_index)
                .collect::<Vec<_>>()
        );

        let id_index = merge
            .target
            .table_catalog
            .columns()
            .iter()
            .position(|column| column.name() == "id")
            .unwrap();
        let v_index = merge
            .target
            .table_catalog
            .columns()
            .iter()
            .position(|column| column.name() == "v")
            .unwrap();

        assert_eq!(merge.clauses.len(), 2);
        assert_eq!(merge.clauses[0].kind, BoundMergeClauseKind::Matched);
        assert_eq!(merge.clauses[1].kind, BoundMergeClauseKind::NotMatched);

        let BoundMergeAction::Update { assignments } = &merge.clauses[0].action else {
            panic!("expected update action");
        };
        assert_eq!(assignments.len(), 1);
        assert_eq!(assignments[0].target_table_column_index, v_index);

        let BoundMergeAction::Insert {
            target_table_column_indices,
            values,
        } = &merge.clauses[1].action
        else {
            panic!("expected insert action");
        };
        assert_eq!(target_table_column_indices, &vec![id_index, v_index]);
        assert_eq!(values.len(), 2);
    }

    #[tokio::test]
    async fn bind_merge_rejects_source_qualified_update_target() {
        let frontend = LocalFrontend::new(FrontendOpts::default()).await;
        frontend
            .run_sql("create table target (id int primary key, v int);")
            .await
            .unwrap();
        frontend
            .run_sql("create table source (id int primary key, v int);")
            .await
            .unwrap();

        let session = frontend.session_ref();
        let mut binder = Binder::new_for_batch(&session);
        let stmt = parse_sql_statements(
            "merge into target as t using source as s on t.id = s.id \
             when matched then update set s.v = t.v",
        )
        .unwrap()
        .remove(0);

        let err = binder.bind(stmt).unwrap_err();
        assert!(
            err.to_string()
                .contains("MERGE target column qualifier must refer to the target table or alias")
        );
    }

    #[tokio::test]
    async fn bind_merge_accepts_target_alias_in_update_target_and_conditions() {
        let frontend = LocalFrontend::new(FrontendOpts::default()).await;
        frontend
            .run_sql("create table target (id int primary key, v int);")
            .await
            .unwrap();
        frontend
            .run_sql("create table source (id int primary key, v int);")
            .await
            .unwrap();

        let session = frontend.session_ref();
        let mut binder = Binder::new_for_batch(&session);
        let stmt = parse_sql_statements(
            "merge into target as t using source as s on t.id = s.id \
             when matched and t.v < s.v then update set t.v = s.v \
             when not matched and s.v > 0 then insert (id, v) values (s.id, s.v)",
        )
        .unwrap()
        .remove(0);

        let bound = binder.bind(stmt).unwrap();
        let BoundStatement::Merge(merge) = bound else {
            panic!("expected BoundStatement::Merge");
        };
        assert_eq!(merge.clauses.len(), 2);
        assert!(merge.clauses.iter().all(|clause| clause.condition.is_some()));
    }
}
