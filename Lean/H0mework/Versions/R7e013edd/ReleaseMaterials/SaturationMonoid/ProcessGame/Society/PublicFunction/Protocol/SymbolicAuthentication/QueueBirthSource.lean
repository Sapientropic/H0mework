import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeBirthWord

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueBirthSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

/-- This is computed from actual source cost words, which need not fit actionLimit. -/
def cost (code : Code Party Good Port (Mandate.State Party Technology) Instrument) : Nat :=
  ((List.finRange code.sites).map fun recipient => (code.deliveryCost recipient).length).sum

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_actual_recipient_cost_is_in_the_source_envelope (recipient : Fin code.sites) :
    (code.deliveryCost recipient).length ≤ cost code := by
  apply List.single_le_sum (fun _ _ => Nat.zero_le _)
  exact List.mem_map.mpr ⟨recipient, List.mem_finRange _, rfl⟩

abbrev protocols : Nat → Rule code := fun _ => SilentWindow.quiet
abbrev row (origin cursor : Cursor code) := OriginQueue.row origin cursor (protocols (code := code))
abbrev state (origin cursor : Cursor code) := OriginQueue.state origin cursor (protocols (code := code))
abbrev rank (origin cursor : Cursor code) := OriginQueue.rank origin cursor (protocols (code := code))
abbrev stages (origin : Cursor code) := OriginQueue.stages origin (protocols (code := code))

theorem a_wait_submits_nothing_or_its_actual_fresh_packet_cost (origin cursor : Cursor code) (count : Nat) :
    (row origin cursor count).submitted = [] ∨
      ∃ event serial packet,
        decision code (EventStep.applied (OriginQueue.cursorAt origin cursor protocols count)
          SilentWindow.quiet (OriginQueue.environment origin)) (state origin cursor count) = some event ∧
        event.val = .deliver serial ∧
        serial ∈ QueueScheduler.untried code (OriginQueue.baseline origin) (state origin cursor count).past ∧
        (state origin cursor count).frame.sent[serial]? = some packet ∧
        (row origin cursor count).submitted = code.deliveryCost packet.recipient := by
  let here := OriginQueue.cursorAt origin cursor protocols count
  have submittedWord := (StageTrace.material_is_the_actual_step here SilentWindow.quiet (OriginQueue.environment origin)).2
  change (row origin cursor count).submitted = Feedback.word code _ _ _ at submittedWord
  by_cases stopped : (EventStep.seed here).remaining = 0
  · left
    rw [submittedWord]
    simp only [word, decision, if_pos stopped]
  · cases own : Distributed.Recall.Information.Agency.ownerAt code here.ownerStart (EventStep.seed here).history.length with
    | some site =>
      left
      rw [submittedWord]
      simp only [word, decision, if_neg stopped, Cursor.controller, driver, own, localEvent, SilentWindow.quiet]
    | none =>
      cases chosen : OriginQueue.environment origin (state origin cursor count).history
          (state origin cursor count).past (state origin cursor count).frame with
      | none =>
        change OriginQueue.environment origin (EventStep.seed here).history (EventStep.seed here).past (EventStep.seed here).frame = none at chosen
        left
        rw [submittedWord]
        simp only [word, decision, if_neg stopped, Cursor.controller, driver, own, chosen,
          Distributed.Recall.Information.Agency.externalChoice]
      | some event =>
        obtain ⟨serial, kind, present, fresh⟩ := QueueScheduler.generated_move_has_actual_queue_and_fresh_address
          code (OriginQueue.baseline origin) _ _ _ event chosen
        let packet := (state origin cursor count).frame.sent[serial]
        have lookup : (state origin cursor count).frame.sent[serial]? = some packet := List.getElem?_eq_getElem present
        change (EventStep.seed here).frame.sent[serial]? = some packet at lookup
        have actualChoice : OriginQueue.environment origin (EventStep.seed here).history (EventStep.seed here).past (EventStep.seed here).frame = some event := chosen
        have admitted : decision code (EventStep.applied here SilentWindow.quiet (OriginQueue.environment origin))
            (EventStep.seed here) = some event := by
          simp only [decision, if_neg stopped, Cursor.controller, driver, own, actualChoice,
            Distributed.Recall.Information.Agency.externalChoice, kind]
        refine Or.inr ⟨event, serial, packet, admitted, kind, fresh, lookup, ?_⟩
        rw [submittedWord]
        simp only [word, admitted, stepLocal, kind, Code.step, lookup, List.nil_append]

theorem every_actual_wait_pays_its_word_from_a_strict_address_decrease
    (origin cursor : Cursor code) (fits : OriginQueue.baseline origin ≤ (EventStep.seed cursor).past.length)
    (count : Nat) :
    (row origin cursor count).submitted.length + rank origin cursor (count + 1) * cost code ≤
      rank origin cursor count * cost code := by
  have monotone := Finset.card_le_card (OriginQueue.later_untried_is_a_subset origin cursor protocols fits count (count + 1) (by omega))
  change rank origin cursor (count + 1) ≤ rank origin cursor count at monotone
  rcases a_wait_submits_nothing_or_its_actual_fresh_packet_cost origin cursor count with empty | actual
  · rw [empty, List.length_nil, Nat.zero_add]
    exact Nat.mul_le_mul_right _ monotone
  · obtain ⟨event, serial, packet, chosen, kind, fresh, _, submitted⟩ := actual
    have bounded := fits.trans (OriginQueue.memory_and_queue_extend origin cursor protocols 0 count (Nat.zero_le _)).1.length_le
    have next : (state origin cursor (count + 1)).past = (state origin cursor count).past ++ [.deliver serial] := by
      change (EventStep.seed ((OriginQueue.cursorAt origin cursor protocols count).after _ _)).past = _
      rw [EventStep.actual_next_state, event_memory_is_extended code _ _ _ event chosen, kind]
    have strict := QueueScheduler.delivered_address_strictly_decreases_the_source_rank code _ _ bounded serial fresh
    change (QueueScheduler.untried code _ (state origin cursor count).past).card > _ at strict
    rw [← next] at strict
    change rank origin cursor (count + 1) < rank origin cursor count at strict
    rw [submitted]
    have one := every_actual_recipient_cost_is_in_the_source_envelope (code := code) packet.recipient
    have paid := Nat.mul_le_mul_right (cost code) (Nat.succ_le_of_lt strict)
    rw [Nat.succ_mul] at paid
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueBirthSource
