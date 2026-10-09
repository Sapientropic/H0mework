import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Source
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.Consumer
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Consumer

set_option autoImplicit false
noncomputable section
universe u v w z
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery
open RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarCochain
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)

theorem core_environment :
    (fun target name => (sourceEnvironment root visit recognition target (name, .old))) =
      (Branch.raw root visit recognition).environment := by
  funext target name
  change (Relation.mixed root visit recognition target (name, .old),
    (Relation.Action.environment root visit recognition - Relation.mixed root visit recognition) target (name, .old)) = _
  rw [Relation.Action.source_environment]
  rfl

theorem core_read : (coreTerm root visit recognition).eval (sourceEnvironment root visit recognition) =
    (Branch.raw root visit recognition).expression.eval (Branch.raw root visit recognition).environment := by
  change ((Branch.raw root visit recognition).expression.subst
    (fun _ name => .var (name, UpdatePart.old))).eval (sourceEnvironment root visit recognition) = _
  rw [Expr.eval_subst]
  exact congrArg (Branch.raw root visit recognition).expression.eval (core_environment root visit recognition)

theorem relation_read : (relationTerm root visit recognition).eval (sourceEnvironment root visit recognition) =
    ((Relation.relationExpression root visit recognition).eval (Relation.mixed root visit recognition),
      (Relation.relationExpression root visit recognition).effect (Relation.mixed root visit recognition)
        (increment root visit recognition)) :=
  eval_liftExpr _ _ _

theorem query_core : (expression root visit recognition).eval (environment root visit recognition) 0 =
    (Branch.raw root visit recognition).expression.eval (Branch.raw root visit recognition).environment := by
  have generated := InventoryVector.query_read (Fin 2) (items root visit recognition)
    (sourceEnvironment root visit recognition) 0
  simpa [expression, environment, items, core_read root visit recognition] using generated

theorem query_relation : (expression root visit recognition).eval (environment root visit recognition) 1 =
    ((Relation.relationExpression root visit recognition).eval (Relation.mixed root visit recognition),
      (Relation.relationExpression root visit recognition).effect (Relation.mixed root visit recognition)
        (increment root visit recognition)) := by
  have generated := InventoryVector.query_read (Fin 2) (items root visit recognition)
    (sourceEnvironment root visit recognition) 1
  simpa [expression, environment, items, relation_read root visit recognition] using generated

theorem core_inventory : (expression root visit recognition).eval (environment root visit recognition) 0 =
    (Finsupp.single (Branch.outcome root visit recognition) 1,
      Finsupp.single (Branch.nextOutcome root visit recognition) 1 -
        Finsupp.single (Branch.outcome root visit recognition) 1) :=
  (query_core root visit recognition).trans (Branch.raw_inventory root visit recognition)

theorem relation_updated_zero : (Relation.relationExpression root visit recognition).eval
    (Relation.Action.environment root visit recognition) = 0 := by
  rw [Relation.Action.source_environment]
  exact (SourceOperationExecution.Coefficients.expression_eval _ _).trans
    (evaluation_updateWord _ _ _)

theorem relation_effect_zero : (Relation.relationExpression root visit recognition).effect
    (Relation.mixed root visit recognition) (increment root visit recognition) = 0 := by
  have generated := (Relation.relationExpression root visit recognition).eval_update
    (Relation.mixed root visit recognition) (increment root visit recognition)
  rw [show Relation.mixed root visit recognition + increment root visit recognition =
      Relation.Action.environment root visit recognition from add_sub_cancel _ _] at generated
  simpa only [relation_updated_zero, Relation.compiled_relation_zero, zero_add] using generated.symm

theorem relation_inventory : (expression root visit recognition).eval (environment root visit recognition) 1 = (0, 0) := by
  rw [query_relation, Relation.compiled_relation_zero, relation_effect_zero]

private theorem lift_remaining {Sorts : Type v} {Carrier : Sorts → Type w} {Names : Sorts → Type z}
    [∀ sort, AddCommGroup (Carrier sort)] {sort : Sorts} (term : Expr Carrier Names sort) :
    remaining (liftExpr term) = remaining term := by
  induction term with
  | var => rfl
  | const => rfl
  | add left right first second => simp only [liftExpr, remaining, first, second]
  | linear f argument previous => simp only [liftExpr, remaining, previous]
  | bilinear f left right first second => simp only [liftExpr, remaining, first, second]

theorem query_charge : remaining (expression root visit recognition) =
    remaining (coreTerm root visit recognition) + remaining (relationTerm root visit recognition) + 4 := by
  rw [InventoryVector.query_charge]
  simp only [items, InventoryVector.charge]
  omega

theorem complete_charge : (trace root visit recognition).length =
    remaining (Branch.raw root visit recognition).expression +
      SourceOperationExecution.Coefficients.cost (Relation.relationWord root visit recognition) + 4 := by
  rw [trace, execution_length, query_charge, relationTerm, lift_remaining,
    Relation.relationExpression,
    SourceOperationExecution.Coefficients.expression_remaining]
  rfl

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
