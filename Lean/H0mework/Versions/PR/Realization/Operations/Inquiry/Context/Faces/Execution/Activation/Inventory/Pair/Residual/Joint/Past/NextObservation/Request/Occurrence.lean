import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Execution
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
namespace J
export RootGeneratedDebtActivationJointSource (initialEvent mathAction)
export RootGeneratedDebtActivationJointSource.Successor (read? Packet join join_whole_paid)
end J

def occurrenceResult {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=current)) :=
  Joint.queryResult seed frame supplied

def occurrenceRaw {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=current)) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort) :=
  let original := occurrenceResult seed frame supplied
  let currentRaw := Joint.queryReader seed frame supplied
  let cursor := (Action.sourceCursor frame supplied).next
  let nextEnvironment := pairEnvironment cursor.next.raw.environment
    (cursor.next.next.raw.environment - cursor.next.raw.environment)
  let request : Expr (PairValue PhysicalValue) PhysicalVar sort :=
    .add currentRaw.expression (.linear (-AddMonoidHom.id _) original.2.1.1)
  ⟨nextEnvironment,request⟩
def occurrenceExecuted {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=current)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
    (Mother.baseState {frame with depth:=0}).root.toAuthoritativeRoot
    (occurrenceRaw seed frame) supplied
def occurrenceWritten {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=current)) :=
  SourceHistoryCommon.seed (Joint.completeWrittenInventory seed frame supplied)
    (SourceOperationPaidRelations.exposure (occurrenceExecuted seed frame supplied).2.1.2)
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
