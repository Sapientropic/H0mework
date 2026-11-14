import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovation.RequestRelay.Effect

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation.Integrated.CP777Independent

open SourceOperationEffects SourceOperationScalarInventoryLift
open SourceOperationInquiry.Context.Installation (executedEnvironmentIncrement)
open scoped InnerProductSpace

private def the_actual_origin_read_returns_its_literal_request_address
    {Sorts : Type u} {V X : Sorts → Type u} [∀ t, AddCommGroup (V t)] {sort : Sorts}
    (start : ℕ) (events : List (SourceInventoryExecutionFeed.Event (V := V) (X := X) (s := sort)))
    (ordinal : Fin (SourceInventoryExecutionFeed.requestsFrom start events).length) :=
  let origin := SourceInventoryExecutionFeed.readRequestOrigin start events ordinal
  And.intro (SourceInventoryExecutionFeed.request_index_at_origin start events ordinal)
    (SourceInventoryExecutionFeed.request_index_at_read start events origin.eventIndex origin.itemIndex)

section AtPacket
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K) (packet next : RelayPacket (K := K) X)
variable (literal : next = Action.packetTransport packet.2.2.2.down (Action.sourceBorn (factory read) packet))

private structure InstalledAddress where
  prior : SourceInventoryExecutionFeed.Inventory (V := L.Value (W K) packet.1) (X := X) (s := .joint)
  present : packet.2.1.1.inventory = some prior
  event : Fin prior.trace.length
  item : Fin (Feed.eventItems (relayedEvent read packet next literal prior present event)).length

variable (address : InstalledAddress read packet next literal)

set_option cleanup.letToHave false in
private def paidBlockAt :=
  let moved := nextInventoryBlock read packet next literal address.prior address.present
  And.intro literal <|
  And.intro moved.2.trace_eq <|
  And.intro (relayed_event_lift read packet next literal address.prior address.present address.event)
    (relayed_request_read read packet next literal address.prior address.present address.event address.item)

set_option cleanup.letToHave false in
private def paidRowAt :=
  let frame := A.epoch next.2.1.1
  let occurrence := S.actualOccurrence next.2.1.1
  let index := relayedRequest read packet next literal address.prior address.present address.event address.item
  let material := I.materialAt frame occurrence
  let increment := executedEnvironmentIncrement frame occurrence
  let entry := (Feed.eventItems (relayedEvent read packet next literal address.prior address.present address.event)).get address.item
  let environment := Native.environmentTransport next.2.2.2.down
    (Request.input (R.actualMaterial next.2.1.1 next.2.2.1)).environment
  let feature := featureEnvironment next.1 environment
  let total := fun target name => (feature target name).1+(feature target name).2
  let value := (JointMeasured.inputTerm read).eval (J.decode (total .joint PUnit.unit))
  have executed := relayed_column_action read packet next literal address.prior address.present address.event address.item
  have row : columnActionRhs read next.1 frame occurrence value index =
      inner ℂ (entry.2 • columnRead read next.1 (entry.1.eval material.raw.environment,0)) value +
        inner ℂ (entry.2 • columnRead read next.1 (0,entry.1.effect material.raw.environment increment)) value := by
    change inner ℂ (columnAction read next.1 frame occurrence index).1 value +
      inner ℂ (columnAction read next.1 frame occurrence index).2 value = _
    rw [executed]
  And.intro executed <| And.intro row (column_action_equation read next.1 frame occurrence value)

private def paidOriginAt :=
  request_origin next.1 (A.epoch next.2.1.1)
    (relayedRequest read packet next literal address.prior address.present address.event address.item)
end AtPacket

section Actual
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K) (sourceFrame : JointMeasured.Frame (K := K)) (ordinal : ℕ)

local notation "oldPacket" => site read sourceFrame ordinal
local notation "nextPacket" => site read sourceFrame (ordinal+1)
local notation "actualNext" => next_packet_is_actual read sourceFrame ordinal

private abbrev InstalledAddressAt := InstalledAddress read oldPacket nextPacket actualNext
variable (address : InstalledAddressAt read sourceFrame ordinal)

set_option cleanup.letToHave false in
private def the_original_written_inventory_keeps_the_lifted_event_and_its_exact_position :=
  paidBlockAt read oldPacket nextPacket actualNext address

set_option cleanup.letToHave false in
private def the_relayed_signed_item_pays_the_next_actual_Gram_rhs_and_literal_write :=
  And.intro (paidRowAt read oldPacket nextPacket actualNext address)
    (actual_next_from_column_actions read sourceFrame (ordinal+1))

set_option cleanup.letToHave false in
private def the_same_next_site_keeps_both_inventories_whole_next_and_request_origin :=
  And.intro (next_inventory_is_actual read sourceFrame ordinal) <|
  And.intro (next_pair_inventory_is_actual read sourceFrame ordinal) <|
  And.intro (next_stock_from_actual_born read sourceFrame ordinal) <|
  And.intro (completed_whole read sourceFrame (ordinal+1)) <|
  And.intro (completed_next read sourceFrame (ordinal+1))
    (paidOriginAt read oldPacket nextPacket actualNext address)
end Actual

open SourceInventoryExecutionFeed (Event eventItems requestsFrom)

private abbrev ConcreteEvent := Event (V := fun _ : Unit => ℤ) (X := fun _ : Unit => Unit) (s := ())
private def repeatedEvent : ConcreteEvent := .generator (.const 7)
private def repeatedSource : List ConcreteEvent := [repeatedEvent,repeatedEvent]
private def repeatedTarget : List ConcreteEvent := [repeatedEvent,repeatedEvent,repeatedEvent]
private def repeatedBlock : ActualNativeRelationTransport.OccurrenceBlock repeatedSource repeatedTarget :=
  ⟨[repeatedEvent],[],rfl⟩
private def leftOccurrence : Fin repeatedSource.length := ⟨0,by decide⟩
private def rightOccurrence : Fin repeatedSource.length := ⟨1,by decide⟩
private def leftItem : Fin (eventItems (repeatedSource.get leftOccurrence)).length := ⟨0,by decide⟩
private def rightItem : Fin (eventItems (repeatedSource.get rightOccurrence)).length := ⟨0,by decide⟩

private theorem repeated_event_values_keep_distinct_actual_request_addresses :
    let left := repeatedBlock.requestIndex 0 leftOccurrence leftItem
    let right := repeatedBlock.requestIndex 0 rightOccurrence rightItem
    let first := (requestsFrom 0 repeatedTarget).get left
    let second := (requestsFrom 0 repeatedTarget).get right
    left ≠ right ∧ first.sourceEvent = second.sourceEvent ∧
      first.position = 1 ∧ second.position = 2 ∧ first.coefficient = 1 ∧ second.coefficient = 1 := by
  dsimp only
  have leftRead := repeatedBlock.request_index_read 0 leftOccurrence leftItem
  have rightRead := repeatedBlock.request_index_read 0 rightOccurrence rightItem
  have leftPosition : ((requestsFrom 0 repeatedTarget).get
      (repeatedBlock.requestIndex 0 leftOccurrence leftItem)).position = 1 :=
    congrArg (fun request => request.position) leftRead
  have rightPosition : ((requestsFrom 0 repeatedTarget).get
      (repeatedBlock.requestIndex 0 rightOccurrence rightItem)).position = 2 :=
    congrArg (fun request => request.position) rightRead
  refine ⟨?_,?_,leftPosition,rightPosition,?_,?_⟩
  · intro erased
    have same := congrArg (fun index => ((requestsFrom 0 repeatedTarget).get index).position) erased
    rw [leftPosition,rightPosition] at same
    omega
  · rw [leftRead,rightRead]
    rfl
  · rw [leftRead]
    rfl
  · rw [rightRead]
    rfl

run_cmd do
  IO.println "CP777_CONTROL + the_actual_origin_read_returns_its_literal_request_address\nCP777_CONTROL + the_original_written_inventory_keeps_the_lifted_event_and_its_exact_position\nCP777_CONTROL + the_relayed_signed_item_pays_the_next_actual_Gram_rhs_and_literal_write\nCP777_CONTROL + the_same_next_site_keeps_both_inventories_whole_next_and_request_origin\nCP777_CONTROL - repeated_event_values_keep_distinct_actual_request_addresses\nCP777_GATE_PASS positive=4 negative=1"

end PaidSourceContentEnvironment.GradedInnovation.Integrated.CP777Independent
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
