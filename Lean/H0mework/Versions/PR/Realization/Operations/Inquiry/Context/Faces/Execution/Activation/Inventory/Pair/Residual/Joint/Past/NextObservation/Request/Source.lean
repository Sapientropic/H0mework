import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Consumer
import H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Calculation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace R
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
  (MaterialAt input expression relations budget updated_value residual_value residual_zero_iff)
end R
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
def old := (Shared.baseRoot frame (continuedConfiguration seed)).toAuthoritativeRoot
abbrev origin := (Shared.actualVisit frame).current
abbrev reader := fun (supplied : Context.Installation.Occurrence frame (current:=(Shared.actualVisit frame).current)) =>
  (Shared.datum frame (continuedConfiguration seed)).reader supplied
abbrev calculationRoot := RootGeneratedDebtActivationJointSource.OwnerFree.authoritativeRoot
  (old seed frame) (origin frame) (reader seed frame)
abbrev endpoint := (Shared.resultFace frame (continuedConfiguration seed)).rootRead.2.1
abbrev Occurrence := (calculationRoot seed frame).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt (endpoint seed frame)
def material (supplied : Occurrence seed frame) : R.MaterialAt
    (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort) supplied := by
  rcases supplied with ⟨support,event⟩
  cases event
  let raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort) :=
    (Shared.query frame (continuedConfiguration seed)).raw
  exact {
    environment := raw.environment
    increment := (after seed frame).environment - raw.environment
    raw := raw.expression
    state := endpoint seed frame
    owner := RootGeneratedDebtActivationJointSource.OwnerFree.mathEntry
      (old seed frame) (origin frame) (reader seed frame) (endpoint seed frame) }
def registered := RootGeneratedDebtActivationJointSource.register (fun supplied : Occurrence seed frame =>
  R.input (material seed frame supplied))
abbrev actualMaterial := material seed frame ((calculationRoot seed frame).emitted (endpoint seed frame))
theorem actual_next_environment : (registered seed frame).input.environment = (after seed frame).environment :=
  add_sub_cancel _ _
theorem actual_inventory : (actualMaterial seed frame).environment = (before seed frame).environment ∧
    (actualMaterial seed frame).increment = increment seed frame := by
  constructor
  · exact current_environment seed frame
  · exact congrArg ((after seed frame).environment - ·) (current_environment seed frame)
theorem effect_generated : type_of% (R.updated_value (R:=ℤ) (actualMaterial seed frame)) := R.updated_value (R:=ℤ) (actualMaterial seed frame)
theorem inverse_generated : type_of% (R.residual_value (R:=ℤ) (actualMaterial seed frame)) := R.residual_value (R:=ℤ) (actualMaterial seed frame)
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
