import H0mework.Versions.AD.Realization.Perfectification.Occurrence.Temporal.Action.Source
import H0mework.Realization.Operations.Execution.Relations
import H0mework.Realization.Operations.Execution.Coefficients.Words
import H0mework.Realization.Logic.FibreLift
/-! Actual old and next traces generate the full relation and inverse fibre.
Original integer coefficients produce its executable old/effect syntax. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceTemporalMaterial.Action
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (root : SourceNativeLivingRootClosure N V)
def sourceTrace (code : Code (lower root)) := execution (environment root code) (programme root)
def nextTrace (code : Code (lower root)) := execution (updatedEnvironment root code) (programme root)
abbrev oldWord (code : Code (lower root)) := SourceOperationScalarPresentation.relationMap (R:=ℤ)
  (environment root code) (sourceTrace root code).relationWords
abbrev nextWord (code : Code (lower root)) := SourceOperationScalarPresentation.relationMap (R:=ℤ)
  (updatedEnvironment root code) (nextTrace root code).relationWords
open SourceOperationScalarRelations SourceGeneratedScalarDifferentialResidual
open SourceOperationLogic SourceOperationLogic.FibreLift
abbrev morphism (code : Code (lower root)) := updateMorphism (R:=ℤ) (s:=Slot.result)
  (environment root code) (delta root code)
def target (code : Code (lower root)) : Fibre
    (evaluation (R:=ℤ) (environment root code + delta root code))
    (q (evaluation (R:=ℤ) (environment root code + delta root code)) (oldWord root code)) :=
  ⟨oldWord root code + nextWord root code, by
    apply (q_eq_iff _ _ _).mpr
    rw [LinearMap.mem_ker, add_sub_cancel_left]
    rw [show environment root code + delta root code = updatedEnvironment root code from add_sub_cancel _ _]
    exact (nextTrace root code).relation_old (R:=ℤ)⟩
abbrev reverse (code : Code (lower root)) := liftingResidual (morphism root code) (oldWord root code) (target root code)
def residualRaw (code : Code (lower root)) : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=PairValue (Value root)) (Var:=Var) (sort:=Slot.result) :=
  ⟨pairEnvironment (environment root code) (delta root code),
    liftExpr (SaturationMonoid.SourceOperationExecution.Coefficients.expression (nextWord root code))⟩
theorem oldWord_boundary (code : Code (lower root)) : oldWord root code =
    Finsupp.single (programme root) 1 - Finsupp.single (.const (Finsupp.single (actual root code) 1)) 1 :=
  (sourceTrace root code).relation_boundary.trans (congrArg (fun value =>
    Finsupp.single (programme root) (1 : ℤ) - Finsupp.single (.const value) 1) (programme_value root code))

theorem inverse_read (code : Code (lower root)) :
    (residualEquivRange (evaluation (R:=ℤ) (environment root code + delta root code))
      (canonicalResidual (evaluation (R:=ℤ) (environment root code + delta root code))
        (oldWord root code))).val = (programme root).effect (environment root code) (delta root code) := by
  rw [(sourceTrace root code).updated_residual (R:=ℤ) (delta root code)]
  change effectEvaluator (R:=ℤ) (s:=Slot.result) (environment root code) (delta root code) (oldWord root code) = _
  rw [oldWord_boundary]
  simp only [map_sub, effectEvaluator, Finsupp.linearCombination_single, one_smul, Expr.effect, sub_zero]

theorem reverse_coordinate (code : Code (lower root)) :
    (targetCoordinate (morphism root code) (oldWord root code) (target root code)).val = nextWord root code :=
  add_sub_cancel_left _ _

theorem residual_raw_value (code : Code (lower root)) :
    (residualRaw root code).expression.eval (residualRaw root code).environment =
      updateInventory (R:=ℤ) (environment root code) (delta root code) (nextWord root code) := by
  rw [show (residualRaw root code).expression.eval (residualRaw root code).environment = _ from
    eval_liftExpr (SaturationMonoid.SourceOperationExecution.Coefficients.expression (nextWord root code))
      (environment root code) (delta root code)]
  rw [SaturationMonoid.SourceOperationExecution.Coefficients.expression_eval,
    SaturationMonoid.SourceOperationExecution.Coefficients.expression_effect]
  rfl

end SourceTemporalMaterial.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
