import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryTrace

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryProgress
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open AdaptiveDeliveryTrace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code) (protocols : Nat → Rule code) (rivals : Nat → Opponent code)

abbrev potential (allowance n : Nat) := rank start protocols rivals n * (allowance + 1) +
  (allowance - gap start protocols rivals n)
def external (n : Nat) : Bool := match (row start protocols rivals n).call with
  | .external _ => true
  | _ => false

theorem pending_means_available (n serial : Nat)
    (present : serial < (state start protocols rivals n).frame.sent.length)
    (pending : serial ∈ QueueScheduler.untried code (baseline start) (state start protocols rivals n).past) :
    InterferenceEnvelope.fresh start (cursorAt start protocols rivals n) ≠ [] := by
  have accepted := Finset.mem_sdiff.mp pending
  obtain ⟨event, supported, encoded⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp accepted.1)
  have kind : event = .deliver serial := by cases event <;> simp_all [QueueScheduler.address]
  subst event
  have inside : (⟨.deliver serial, supported⟩ : Choice code) ∈
      InterferenceEnvelope.fresh start (cursorAt start protocols rivals n) := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_attach _ _, decide_eq_true ⟨present, accepted.2⟩⟩
  intro empty
  rw [empty] at inside
  contradiction

theorem progress_decreases_rank (n : Nat)
    (progress : InterferenceEnvelope.progresses start (row start protocols rivals n) = true) :
    rank start protocols rivals (n + 1) < rank start protocols rivals n := by
  unfold InterferenceEnvelope.progresses at progress
  cases called : (row start protocols rivals n).call <;> simp only [called] at progress <;> try contradiction
  rename_i move
  cases admitted : Distributed.Recall.Information.Agency.externalChoice code move with
  | none => rw [admitted] at progress; contradiction
  | some event =>
    rw [admitted] at progress
    have fresh := of_decide_eq_true progress
    obtain ⟨serial, kind, supported, _, missing⟩ :=
      CompletionEnvelope.every_generated_delivery_has_a_real_fresh_admitted_packet start
        (cursorAt start protocols rivals n) event fresh
    have selected : decision code (EventStep.applied (cursorAt start protocols rivals n) (protocols n) (rivals n))
        (state start protocols rivals n) = some event := by
      rw [← StageTrace.captured_admission_is_the_actual_decision]
      change ControlExecution.admitted code (row start protocols rivals n).call = _
      rw [called]; exact admitted
    change (QueueScheduler.untried code (baseline start)
      (EventStep.seed ((cursorAt start protocols rivals n).after _ _)).past).card < _
    rw [EventStep.actual_next_state, event_memory_is_extended code _ _ _ event selected, kind]
    exact QueueScheduler.delivered_address_strictly_decreases_the_source_rank code _ _
      (memory_queue start protocols rivals 0 n (Nat.zero_le _)).1.length_le serial (Finset.mem_sdiff.mpr ⟨supported, missing⟩)

theorem gap_next (n : Nat) : gap start protocols rivals (n + 1) =
    match (row start protocols rivals n).call with
    | .external _ => if (InterferenceEnvelope.available (baseline start) (state start protocols rivals n)).isEmpty ||
        InterferenceEnvelope.progresses start (row start protocols rivals n) then 0 else gap start protocols rivals n + 1
    | _ => gap start protocols rivals n := by
  simp only [gap, records_succ, InterferenceEnvelope.gap, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem a_nonprogress_external_step_uses_only_the_remaining_delay_allowance
    (allowance n serial : Nat) (active : n < (EventStep.seed start).remaining)
    (present : serial < (state start protocols rivals n).frame.sent.length)
    (pending : serial ∈ QueueScheduler.untried code (baseline start) (state start protocols rivals n).past)
    (chosen : InterferenceEnvelope.intake (cursorAt start protocols rivals n) (rivals n) ∈
      InterferenceEnvelope.choices start (stages protocols rivals n) allowance)
    (isExternal : external start protocols rivals n = true)
    (noProgress : InterferenceEnvelope.progresses start (row start protocols rivals n) = false) :
    gap start protocols rivals n < allowance := by
  have live : (state start protocols rivals n).remaining ≠ 0 := by rw [(clocks start protocols rivals n).2.1]; omega
  have owner : Distributed.Recall.Information.Agency.ownerAt code
      (cursorAt start protocols rivals n).ownerStart (state start protocols rivals n).history.length = none := by
    cases own : Distributed.Recall.Information.Agency.ownerAt code
        (cursorAt start protocols rivals n).ownerStart (state start protocols rivals n).history.length with
    | none => rfl
    | some site => simp only [external, row, StageTrace.material, StageTrace.capture, if_neg live, own, Bool.false_eq_true] at isExternal
  have call : (row start protocols rivals n).call = .external
      ((rivals n) (state start protocols rivals n).history (state start protocols rivals n).past (state start protocols rivals n).frame) := by
    simp only [row, StageTrace.material, StageTrace.capture, if_neg live, owner]
  have nonempty := pending_means_available start protocols rivals n serial present pending
  by_contra full
  cases freshEq : InterferenceEnvelope.fresh start (cursorAt start protocols rivals n) with
  | nil => exact nonempty freshEq
  | cons head tail =>
    have selected : InterferenceEnvelope.intake (cursorAt start protocols rivals n) (rivals n) ∈ (head :: tail).map some := by
      unfold InterferenceEnvelope.choices at chosen
      rw [execute_stages] at chosen
      simpa only [owner, Option.isSome_none, Bool.false_eq_true, if_false, freshEq, if_neg full] using chosen
    obtain ⟨event, inside, same⟩ := List.mem_map.mp selected
    have actual : Distributed.Recall.Information.Agency.externalChoice code
        ((rivals n) (state start protocols rivals n).history (state start protocols rivals n).past (state start protocols rivals n).frame) = some event := by
      simpa only [CompletionEnvelope.intake, CompletionEnvelope.raw, owner, Option.isSome_none,
        Bool.false_eq_true, if_false, EventStep.selected] using same.symm
    have progress : InterferenceEnvelope.progresses start (row start protocols rivals n) = true := by
      simp only [InterferenceEnvelope.progresses, call, actual]
      apply decide_eq_true
      change event ∈ InterferenceEnvelope.fresh start (cursorAt start protocols rivals n)
      rw [freshEq]; exact inside
    rw [noProgress] at progress; contradiction

theorem each_pending_external_turn_spends_the_source_generated_potential
    (allowance n serial : Nat) (active : n < (EventStep.seed start).remaining)
    (present : serial < (state start protocols rivals n).frame.sent.length)
    (pending : serial ∈ QueueScheduler.untried code (baseline start) (state start protocols rivals n).past)
    (chosen : InterferenceEnvelope.intake (cursorAt start protocols rivals n) (rivals n) ∈
      InterferenceEnvelope.choices start (stages protocols rivals n) allowance) :
    potential start protocols rivals allowance (n + 1) +
      (if external start protocols rivals n then 1 else 0) ≤ potential start protocols rivals allowance n := by
  have monotone := Finset.card_le_card (later_untried start protocols rivals n (n + 1) (by omega))
  change rank start protocols rivals (n + 1) ≤ rank start protocols rivals n at monotone
  have product := Nat.mul_le_mul_right (allowance + 1) monotone
  have fresh := pending_means_available start protocols rivals n serial present pending
  have nonempty : (InterferenceEnvelope.available (baseline start) (state start protocols rivals n)).isEmpty = false := by
    exact List.isEmpty_eq_false_iff.mpr fresh
  by_cases progress : InterferenceEnvelope.progresses start (row start protocols rivals n) = true
  · have drops := progress_decreases_rank start protocols rivals n progress
    have strictProduct := Nat.mul_le_mul_right (allowance + 1) (Nat.succ_le_of_lt drops)
    rw [Nat.succ_mul] at strictProduct
    have wholeProgress := progress
    cases called : (row start protocols rivals n).call <;>
      simp only [InterferenceEnvelope.progresses, called] at progress <;> try contradiction
    have reset : gap start protocols rivals (n + 1) = 0 := by
      rw [gap_next, called]; simp only [wholeProgress, Bool.or_true, ↓reduceIte]
    simp only [potential, external, called, ↓reduceIte, reset, Nat.sub_zero]
    omega
  · have noProgress : InterferenceEnvelope.progresses start (row start protocols rivals n) = false := Bool.eq_false_iff.mpr progress
    cases called : (row start protocols rivals n).call with
    | external move =>
      have room := a_nonprogress_external_step_uses_only_the_remaining_delay_allowance start protocols rivals allowance n serial
        active present pending chosen (by simp only [external, called]) noProgress
      have advances : gap start protocols rivals (n + 1) = gap start protocols rivals n + 1 := by
        rw [gap_next, called]; simp only [nonempty, noProgress, Bool.false_or, Bool.false_eq_true, if_false]
      simp only [potential, external, called, ↓reduceIte, advances]
      omega
    | stopped =>
      have same : gap start protocols rivals (n + 1) = gap start protocols rivals n := by rw [gap_next, called]
      simpa only [potential, external, called, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, same, Nat.add_zero] using Nat.add_le_add_right product (allowance - gap start protocols rivals n)
    | inherited move =>
      have same : gap start protocols rivals (n + 1) = gap start protocols rivals n := by rw [gap_next, called]
      simpa only [potential, external, called, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, same, Nat.add_zero] using Nat.add_le_add_right product (allowance - gap start protocols rivals n)
    | own site move =>
      have same : gap start protocols rivals (n + 1) = gap start protocols rivals n := by rw [gap_next, called]
      simpa only [potential, external, called, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, same, Nat.add_zero] using Nat.add_le_add_right product (allowance - gap start protocols rivals n)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryProgress
