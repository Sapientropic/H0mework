import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Source
import H0mework.Versions.AE.Realization.Perfectification.Occurrence.Temporal.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
def stage (index : Nat) : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort) := {frame with depth:=index}
abbrev receipt (index : Nat) := SourceTemporalMaterial.encode
  (Shared.root (stage frame index) (configuration seed)).toAuthoritativeRoot.toLedgerRoot
  (Shared.visit (stage frame index) (configuration seed))
abbrev result (index : Nat) := queryResult seed (epoch (stage frame index))
  (Shared.actualOccurrence (stage frame index))
def exposure (index : Nat) := SourceOperationPaidRelations.exposure (result seed frame index).2.1.2
abbrev Packet := Σ index : Nat,
  type_of% (receipt seed frame index) × type_of% (result seed frame index)
def packet (index : Nat) : Packet seed frame := ⟨index,receipt seed frame index,result seed frame index⟩
def material : Nat → RootedAccountedUnfolding (Packet seed frame)
  | 0 => .zero (packet seed frame 0)
  | count+1 => .occur (packet seed frame (count+1)) (.cons (material count) .nil)
def fromPacket (datum : Packet seed frame)
    (children : List (RootedAccountedUnfolding (PresentedRelationEventAt
      (Expr (PairValue PhysicalValue) PhysicalVar sort)))) :=
  children.foldr SourceHistoryCommon.seed (SourceOperationPaidRelations.exposure datum.2.2.2.1.2)
def generate (last : Nat) := (material seed frame last).fold (fromPacket seed frame)
abbrev written := SourceHistoryCommon.seed (generate seed frame frame.depth)
  (completeWrittenInventory seed (epoch frame) (Shared.actualOccurrence frame))
def continuedConfiguration := {configuration seed with
  nextPairInventory := fun sourceFrame => some (written seed sourceFrame)}
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
