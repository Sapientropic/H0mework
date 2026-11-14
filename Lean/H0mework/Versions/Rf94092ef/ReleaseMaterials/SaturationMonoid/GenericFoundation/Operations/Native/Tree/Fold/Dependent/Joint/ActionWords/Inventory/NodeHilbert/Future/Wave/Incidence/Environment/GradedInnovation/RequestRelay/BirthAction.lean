import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory.BirthAction.Receipt

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation.Integrated

open SourceOperationEffects SourceOperationScalarInventoryLift
open SourceOperationInquiry.Context.Installation (executedEnvironmentIncrement)
namespace BirthAction
export ActualCofinalSourceAction (first_birth_local_increment)
export ActualCofinalSourceAction.BirthReceipt (birthRequest birthRequestAction birth_request_action_paid)
export ActualCofinalSourceAction.SourceReceiptOccurrence (ExecutionAt)
end BirthAction

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups

omit [InnerProductSpace ℂ K] in
private theorem preserve_newborn_local_step {Y Z : J.Slot → Type u}
    (native : RelayPacket (K := K) Y) (target : RelayPacket (K := K) Z)
    (language : Y=Z) (literal : Action.packetTransport language native = target)
    (retained : executedEnvironmentIncrement (A.epoch native.2.1.1) (S.actualOccurrence native.2.1.1) = 0) :
    executedEnvironmentIncrement (A.epoch target.2.1.1) (S.actualOccurrence target.2.1.1) = 0 := by
  cases language
  cases literal
  exact retained

omit [InnerProductSpace ℂ K] in
private theorem preserve_signed_execution {Y Z : J.Slot → Type u}
    (native : RelayPacket (K := K) Y) (target : RelayPacket (K := K) Z)
    (language : Y=Z) (literal : Action.packetTransport language native = target)
    (execution : BirthAction.ExecutionAt native) :
    let wrote := execution.reindex native target language literal
    HEq (wrote.request.coefficient • wrote.request.expression.eval wrote.decoder)
      (execution.request.coefficient • execution.request.expression.eval execution.decoder) := by
  cases language
  cases literal
  rfl

variable (read : J.Orbit →ₗ[ℤ] K) (sourceFrame : JointMeasured.Frame (K := K))

theorem actual_first_born_local_increment (ordinal : Nat) :
    let next := site read sourceFrame (ordinal+1)
    executedEnvironmentIncrement (A.epoch next.2.1.1) (S.actualOccurrence next.2.1.1) = 0 := by
  let source := site read sourceFrame ordinal
  let target := site read sourceFrame (ordinal+1)
  have literal := next_packet_is_actual read sourceFrame ordinal
  exact preserve_newborn_local_step (Action.sourceBorn (factory read) source) target source.2.2.2.down literal.symm
    (BirthAction.first_birth_local_increment (factory read) source)

/-- The exact execution branch is installed in the original literal next packet. -/
def actualBirthExecution (ordinal : Nat) :
    let packet : RelayPacket (K := K) X := site read sourceFrame ordinal
    let target : RelayPacket (K := K) X := site read sourceFrame (ordinal+1)
    ∀ (prior : SourceInventoryExecutionFeed.Inventory (V := L.Value (W K) packet.1) (X := X) (s := .joint))
      (_present : packet.2.1.1.inventory = some prior) (event : Fin prior.trace.length)
      (_item : Fin (Feed.eventItems ((prior.trace.map (Action.sourceLiftEvent packet)).get
        (Fin.cast (List.length_map _).symm event))).length),
      BirthAction.ExecutionAt target := by
  intro packet target prior present event item
  let native := Action.sourceBorn (factory read) packet
  let execution := BirthAction.birthRequest (factory read) packet prior present event item
  have literal := next_packet_is_actual read sourceFrame ordinal
  exact execution.reindex native target packet.2.2.2.down literal.symm

theorem actual_birth_receipt_action (ordinal : Nat) :
    let packet : RelayPacket (K := K) X := site read sourceFrame ordinal
    ∀ (prior : SourceInventoryExecutionFeed.Inventory (V := L.Value (W K) packet.1) (X := X) (s := .joint))
      (present : packet.2.1.1.inventory = some prior) (event : Fin prior.trace.length)
      (item : Fin (Feed.eventItems ((prior.trace.map (Action.sourceLiftEvent packet)).get
        (Fin.cast (List.length_map _).symm event))).length),
    let actual := actualBirthExecution read sourceFrame ordinal prior present event item
    let effect := BirthAction.birthRequestAction (factory read) packet prior present event item
    HEq (actual.request.coefficient • actual.request.expression.eval actual.decoder) (effect.1+effect.2) := by
  intro packet prior present event item actual effect
  let native := Action.sourceBorn (factory read) packet
  let target := site read sourceFrame (ordinal+1)
  let execution := BirthAction.birthRequest (factory read) packet prior present event item
  have literal := next_packet_is_actual read sourceFrame ordinal
  have readback := preserve_signed_execution native target packet.2.2.2.down literal.symm execution
  have paid := BirthAction.birth_request_action_paid (factory read) packet prior present event item
  exact readback.trans (heq_of_eq paid)

end PaidSourceContentEnvironment.GradedInnovation.Integrated
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
