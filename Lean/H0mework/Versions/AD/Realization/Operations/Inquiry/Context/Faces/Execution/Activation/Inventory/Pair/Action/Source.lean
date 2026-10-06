import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Physical.Consumer
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Source

/-! Two successive original physical actions generate the updated pair environment
at the supplied occurrence. No computed query result or future table enters it. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Action
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
def sourceNextEnvironment :=
  (physical frame occurrence).nextRaw.environment
-- This existing cursor is used only for its physical action restriction.
abbrev sourceCursor := Context.Native.Orbit.Installation.cursorAt frame occurrence
abbrev secondEnvironment := (sourceCursor frame occurrence).next.next.raw.environment

abbrev updatedPairEnvironment := pairEnvironment (sourceNextEnvironment frame occurrence)
  (secondEnvironment frame occurrence - sourceNextEnvironment frame occurrence)

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
