import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Source
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.Source
import H0mework.Realization.Logic.FibreLift
import H0mework.Realization.Logic.QuantifiedUpdate
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
open SourceGeneratedScalarDifferentialResidual SourceOperationLogic SourceOperationLogic.FibreLift
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
theorem actual_equation : (originalValue seed frame).1 + (originalValue seed frame).2 = actualTarget seed frame :=
  (LinearMap.congr_fun (morphism seed frame).commutes (word seed frame))

theorem inverse_exact (target : Fibre (updated seed frame) (q (updated seed frame) (word seed frame))) :
    residual seed frame target = 0 ↔
      ∃ representative : Fibre (full seed frame) (q (full seed frame) (word seed frame)),
        inverse seed frame representative = target :=
  liftingResidual_eq_zero_iff _ _ _
theorem current_word_source : (word seed frame) =
    Finsupp.single (queryRaw seed (epoch frame) (Shared.actualOccurrence frame)
      (disposition seed (epoch frame) (Shared.actualOccurrence frame))).expression (1 : ℤ) := rfl

theorem actual_next_source : actualNext seed frame = Shared.next frame (continuedConfiguration seed) := rfl

theorem current_environment : (Shared.query frame (continuedConfiguration seed)).raw.environment =
    (before seed frame).environment := by
  change (queryRaw seed (epoch frame) (Shared.actualOccurrence frame)
    (disposition seed (epoch frame) (Shared.actualOccurrence frame))).environment = _
  generalize disposition seed (epoch frame) (Shared.actualOccurrence frame) = phase
  cases phase <;> rfl

theorem current_value : (originalValue seed frame).1 =
    (Shared.resultFace frame (continuedConfiguration seed)).rootRead.2.2.1 := by
  have generated := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (Shared.baseRoot frame (continuedConfiguration seed)).toAuthoritativeRoot
    (fun {current} => (Shared.datum frame (continuedConfiguration seed)).reader)
    ((Shared.root frame (continuedConfiguration seed)).emitted (Shared.visit frame (continuedConfiguration seed)).current)
  have evaluationValue : (originalValue seed frame).1 =
      (Shared.query frame (continuedConfiguration seed)).raw.expression.eval (before seed frame).environment := by
    change evaluation (R:=ℤ) (before seed frame).environment (word seed frame) = _
    exact (Finsupp.linearCombination_single (R:=ℤ)
      (v:=fun expression : Expr (PairValue PhysicalValue) PhysicalVar sort =>
        expression.eval (before seed frame).environment)
      1 (Shared.query frame (continuedConfiguration seed)).raw.expression).trans
      (one_smul ℤ _)
  exact evaluationValue.trans ((congrArg
    (fun binding => (Shared.query frame (continuedConfiguration seed)).raw.expression.eval binding)
    (current_environment seed frame).symm).trans generated.symm)

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
