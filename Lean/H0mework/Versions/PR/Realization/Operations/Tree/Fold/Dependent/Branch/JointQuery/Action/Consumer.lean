import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Action.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action
open RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)

theorem source_environment : sourceEnvironment root visit recognition =
    InventoryVector.environment (Fin 2)
      (pairEnvironment (Relation.Action.environment root visit recognition)
        (followingMixed root visit recognition - Relation.Action.environment root visit recognition)) := by
  funext target name index
  cases target with
  | origin =>
      rcases name with ⟨datum, coordinate⟩
      cases coordinate <;> rfl
  | result => exact PEmpty.elim name.1
  | children => exact PEmpty.elim name.1

theorem actualEquation : (expression root visit recognition).eval (JointQuery.environment root visit recognition) =
    (JointQuery.expression root visit recognition).eval (sourceEnvironment root visit recognition) :=
  Expr.eval_subst _ _ _

theorem environment_update : JointQuery.environment root visit recognition + increment root visit recognition =
    sourceEnvironment root visit recognition := add_sub_cancel _ _

theorem actual_update : (expression root visit recognition).eval (JointQuery.environment root visit recognition) =
    (JointQuery.expression root visit recognition).eval (JointQuery.environment root visit recognition) +
      (JointQuery.expression root visit recognition).effect (JointQuery.environment root visit recognition)
        (increment root visit recognition) := by
  rw [actualEquation, ← environment_update]
  exact Expr.eval_update _ _ _

private theorem binding_remaining (target : SourceOperationNative.Tree.Fold.Slot)
    (name : JointQuery.Variable root visit recognition target) :
    remaining (binding root visit recognition target name) = 1 := by
  cases target with
  | origin => rfl
  | result => exact PEmpty.elim name.1
  | children => exact PEmpty.elim name.1

private theorem expression_remaining {target : SourceOperationNative.Tree.Fold.Slot}
    (term : Expr (JointQuery.Value root visit recognition) (JointQuery.Variable root visit recognition) target) :
    remaining (term.subst (binding root visit recognition)) = remaining term := by
  induction term with
  | var name => exact binding_remaining root visit recognition _ name
  | const => rfl
  | add left right first second => simp only [Expr.subst, remaining, first, second]
  | linear f argument previous => simp only [Expr.subst, remaining, previous]
  | bilinear f left right first second => simp only [Expr.subst, remaining, first, second]

theorem full_trace_charge : (fullTrace root visit recognition).length =
    remaining (raw root visit recognition).expression :=
  substituted_charge _ _ _

theorem full_charge : (fullTrace root visit recognition).length =
    remaining (Branch.raw root visit recognition).expression +
      SourceOperationExecution.Coefficients.cost (Relation.relationWord root visit recognition) + 4 := by
  rw [full_trace_charge]
  change remaining ((JointQuery.expression root visit recognition).subst (binding root visit recognition)) = _
  rw [expression_remaining]
  exact (execution_length _ _).symm.trans (JointQuery.complete_charge root visit recognition)

theorem material_origin : (material root visit recognition).1 = Relation.Action.material root visit recognition := rfl

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
