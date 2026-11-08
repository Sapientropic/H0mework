import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueMemoryEffect

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueMemoryDeadline
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (origin cursor : Cursor code) (protocols : Nat → Rule code)

abbrev horizon := OriginQueue.horizon origin cursor
abbrev row := OriginQueue.row origin cursor protocols

def locate (serial : Nat) : Option Nat :=
  (List.range (horizon origin cursor)).find? fun index => StageReception.delivered (row origin cursor protocols index) serial

theorem every_location_is_an_actual_source_delivery (serial index : Nat)
    (selected : locate origin cursor protocols serial = some index) :
    index < horizon origin cursor ∧ StageReception.delivered (row origin cursor protocols index) serial = true := by
  unfold locate at selected
  have member := List.mem_of_find?_eq_some selected
  have actual := List.find?_some selected
  exact ⟨List.mem_range.mp member, actual⟩

theorem the_original_source_generates_its_delivery_location
    (fits : OriginQueue.baseline origin ≤ (EventStep.seed cursor).past.length)
    (serial : Nat) (enough : horizon origin cursor ≤ (EventStep.seed cursor).remaining)
    (present : serial < (EventStep.seed cursor).frame.sent.length)
    (fresh : serial ∈ QueueScheduler.untried code (OriginQueue.baseline origin) (EventStep.seed cursor).past) :
    ∃ index, locate origin cursor protocols serial = some index ∧ index < horizon origin cursor ∧
      StageReception.delivered (row origin cursor protocols index) serial = true := by
  obtain ⟨index, bound, actual⟩ := OriginQueue.the_source_window_generates_an_actual_delivery_attempt
    origin cursor protocols fits serial enough present fresh
  cases selected : locate origin cursor protocols serial with
  | some found =>
    have sound := every_location_is_an_actual_source_delivery origin cursor protocols serial found selected
    exact ⟨found, rfl, sound⟩
  | none =>
    have missing := List.find?_eq_none.mp selected index (List.mem_range.mpr bound)
    rw [actual] at missing
    contradiction

theorem the_initial_packet_is_the_same_packet_at_every_actual_attempt
    (serial : Nat) (packet : code.Packet)
    (present : serial < (EventStep.seed cursor).frame.sent.length)
    (initial : (EventStep.seed cursor).frame.sent[serial]? = some packet) (index : Nat) :
    (row origin cursor protocols index).before.frame.sent[serial]? = some packet := by
  obtain ⟨more, same⟩ := (OriginQueue.memory_and_queue_extend origin cursor protocols 0 index (Nat.zero_le _)).2
  change (EventStep.seed cursor).frame.sent ++ more = (OriginQueue.state origin cursor protocols index).frame.sent at same
  change (OriginQueue.state origin cursor protocols index).frame.sent[serial]? = some packet
  rw [← same, List.getElem?_append, if_pos present]
  exact initial

theorem the_source_deadline_generates_paid_recovery_or_the_original_fee_refusal
    (fits : OriginQueue.baseline origin ≤ (EventStep.seed cursor).past.length)
    (serial : Nat) (packet : code.Packet)
    (enough : horizon origin cursor ≤ (EventStep.seed cursor).remaining)
    (present : serial < (EventStep.seed cursor).frame.sent.length)
    (initial : (EventStep.seed cursor).frame.sent[serial]? = some packet)
    (fresh : serial ∈ QueueScheduler.untried code (OriginQueue.baseline origin) (EventStep.seed cursor).past)
    (interface : QueueMemoryEffect.restores packet = true) :
    ∃ index, locate origin cursor protocols serial = some index ∧ index < horizon origin cursor ∧
      StageReception.delivered (row origin cursor protocols index) serial = true ∧
      (row origin cursor protocols index).before.frame.sent[serial]? = some packet ∧
      (row origin cursor protocols index).submitted = code.deliveryCost packet.recipient ∧
      QueueMemoryEffect.Resolution (row origin cursor protocols index) serial packet := by
  obtain ⟨index, selected, bound, delivered⟩ := the_original_source_generates_its_delivery_location
    origin cursor protocols fits serial enough present fresh
  have packetAt := the_initial_packet_is_the_same_packet_at_every_actual_attempt origin cursor protocols serial packet present initial index
  have physical := OriginQueue.row_at_its_actual_index origin cursor protocols (horizon origin cursor) index bound
  have member := List.mem_of_getElem? physical
  have words := StageReception.actual_delivery_submits_the_original_cost cursor
    (OriginQueue.stages origin protocols (horizon origin cursor)) (row origin cursor protocols index) member serial packet packetAt delivered
  exact ⟨index, selected, bound, delivered, packetAt, words,
    QueueMemoryEffect.the_actual_delivery_generates_recovery_or_its_exact_payment_obstruction
      (OriginQueue.cursorAt origin cursor protocols index) (protocols index, OriginQueue.environment origin)
      serial packet packetAt delivered interface⟩

theorem the_located_delivery_is_a_native_occurrence_of_the_same_final_source
    (serial index : Nat) (selected : locate origin cursor protocols serial = some index) :
    let actual := row origin cursor protocols index
    let final := EventHistory.execute cursor (OriginQueue.stages origin protocols (horizon origin cursor))
    actual.before.current = final.source.currentAt (EventStep.boundary actual.cursor) ∧
      actual.submitted = ProgrammeSource.rawEvent final.source.input
        (ProgrammeHistory.visitAt final.source.input (EventStep.boundary actual.cursor)).current ∧
      actual.after.current = final.source.currentAt (EventStep.boundary actual.cursor + 1) ∧
      actual.after.current = code.law.next actual.before.current actual.submitted := by
  have physical := OriginQueue.row_at_its_actual_index origin cursor protocols (horizon origin cursor) index
    (every_location_is_an_actual_source_delivery origin cursor protocols serial index selected).1
  exact StageTrace.every_record_is_a_completed_occurrence_of_the_final_source cursor
    (OriginQueue.stages origin protocols (horizon origin cursor)) (row origin cursor protocols index) (List.mem_of_getElem? physical)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueMemoryDeadline
