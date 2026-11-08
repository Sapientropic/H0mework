import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryReceipt

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveReceptionBudget
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open AdaptiveDeliveryTrace AdaptiveDeliveryDeadline

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def delivery (row : StageTrace.Record (code := code)) : Bool :=
  match StageTransport.admission row with
  | some event => match event.val with | .deliver _ => true | _ => false
  | none => false

theorem a_real_delivery_has_an_external_callback (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (delivered : delivery (StageTrace.material cursor protocol rival) = true) :
    ∃ move, (StageTrace.material cursor protocol rival).call = .external move := by
  by_cases stopped : (EventStep.seed cursor).remaining = 0
  · simp only [delivery, StageTransport.admission, StageTrace.material, StageTrace.capture,
      if_pos stopped, ControlExecution.admitted, Bool.false_eq_true] at delivered
  · cases owner : Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart
        (EventStep.seed cursor).history.length with
    | none => exact ⟨EventStep.selected cursor rival, by simp only [StageTrace.material, StageTrace.capture, if_neg stopped, owner]⟩
    | some site =>
      cases selected : localEvent code protocol site ((EventStep.seed cursor).frame.inbox site) with
      | none => simp only [delivery, StageTransport.admission, StageTrace.material, StageTrace.capture,
          if_neg stopped, owner, selected, ControlExecution.admitted, Bool.false_eq_true] at delivered
      | some event =>
        have own := every_local_event_has_its_own_worker code protocol site _ event selected
        simp only [delivery, StageTransport.admission, StageTrace.material, StageTrace.capture,
          if_neg stopped, owner, selected, ControlExecution.admitted] at delivered
        rcases event with ⟨event, supported⟩
        cases event <;> simp_all

theorem every_real_delivery_is_fresh_or_charged (start cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (delivered : delivery (StageTrace.material cursor protocol rival) = true) :
    InterferenceEnvelope.progresses start (StageTrace.material cursor protocol rival) = true ∨
      InterferenceEnvelope.interference start (StageTrace.material cursor protocol rival) = true := by
  obtain ⟨move, call⟩ := a_real_delivery_has_an_external_callback cursor protocol rival delivered
  by_cases fresh : InterferenceEnvelope.progresses start (StageTrace.material cursor protocol rival) = true
  · exact Or.inl fresh
  · right
    have someMove : (Distributed.Recall.Information.Agency.externalChoice code move).isSome = true := by
      simp only [delivery, StageTransport.admission, call, ControlExecution.admitted] at delivered
      cases picked : Distributed.Recall.Information.Agency.externalChoice code move <;> simp_all
    simp only [InterferenceEnvelope.interference, call, someMove, Bool.true_and, Bool.not_eq_true']
    exact Bool.eq_false_iff.mpr fresh

variable (start : Cursor code) (protocols : Nat → Rule code) (rivals : Nat → Opponent code)

def tally (test : StageTrace.Record (code := code) → Bool) (n : Nat) :=
  ((StageTrace.records start (stages protocols rivals n)).filter test).length
abbrev capacity := (QueueScheduler.admitted code).card + code.eventLimit

theorem tally_succ (test : StageTrace.Record (code := code) → Bool) (n : Nat) :
    tally start protocols rivals test (n + 1) = tally start protocols rivals test n +
      (if test (row start protocols rivals n) then 1 else 0) := by
  simp only [tally, records_succ, List.filter_append, List.length_append]
  split <;> simp_all

theorem fresh_deliveries_consume_distinct_source_addresses (n : Nat) :
    tally start protocols rivals (InterferenceEnvelope.progresses start) n + rank start protocols rivals n ≤
      (QueueScheduler.admitted code).card := by
  induction n with
  | zero =>
    change 0 + (QueueScheduler.untried code (baseline start) (state start protocols rivals 0).past).card ≤ _
    simp only [Nat.zero_add]
    exact Finset.card_le_card (Finset.sdiff_subset : QueueScheduler.untried code (baseline start)
      (state start protocols rivals 0).past ⊆ QueueScheduler.admitted code)
  | succ n ih =>
    rw [tally_succ]
    have monotone := Finset.card_le_card (later_untried start protocols rivals n (n + 1) (by omega))
    change rank start protocols rivals (n + 1) ≤ rank start protocols rivals n at monotone
    split
    · have strict := AdaptiveDeliveryProgress.progress_decreases_rank start protocols rivals n (by assumption)
      omega
    · omega

theorem delivery_count_is_paid_by_fresh_addresses_or_actual_interface_spending (n : Nat) :
    tally start protocols rivals delivery n ≤
      tally start protocols rivals (InterferenceEnvelope.progresses start) n +
        InterferenceEnvelope.spent start (stages protocols rivals n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have charged : InterferenceEnvelope.spent start (stages protocols rivals (n + 1)) =
        InterferenceEnvelope.spent start (stages protocols rivals n) +
          if InterferenceEnvelope.interference start (row start protocols rivals n) then 1 else 0 :=
      tally_succ start protocols rivals (InterferenceEnvelope.interference start) n
    rw [tally_succ, tally_succ, charged]
    have paid := every_real_delivery_is_fresh_or_charged start (cursorAt start protocols rivals n) (protocols n) (rivals n)
    cases d : delivery (row start protocols rivals n) <;>
      cases f : InterferenceEnvelope.progresses start (row start protocols rivals n) <;>
      cases c : InterferenceEnvelope.interference start (row start protocols rivals n) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> first | omega | simp_all

theorem every_compliant_adaptive_prefix_has_a_source_generated_reception_budget
    (allowance stop : Nat) (compliant : Compliant start protocols rivals allowance stop) :
    ∀ n ≤ stop, tally start protocols rivals delivery n ≤ capacity (code := code) := by
  intro n bounded
  have charged := AdaptiveDeliveryBudget.every_actual_prefix_keeps_the_one_source_interface_budget
    start protocols rivals allowance stop compliant n bounded
  have fresh := fresh_deliveries_consume_distinct_source_addresses start protocols rivals n
  have paid := delivery_count_is_paid_by_fresh_addresses_or_actual_interface_spending start protocols rivals n
  dsimp only [capacity]; omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveReceptionBudget
