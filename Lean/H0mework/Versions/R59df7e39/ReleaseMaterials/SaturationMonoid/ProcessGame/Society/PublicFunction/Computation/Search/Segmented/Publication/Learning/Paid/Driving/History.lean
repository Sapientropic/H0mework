import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving.Round

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {domain : List (Cursor model.source.code)} {original : Prefix.Rule model.source.code}
  {baseline : Program model.source.code (horizon domain)} {actualHorizon : Nat}
  (state : Paid.State model domain original baseline actualHorizon)
  (reader : Fin model.source.code.sites)
  (unit : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (point : View (code := model.source.code)) (rival : Opponent model.source.code)


/-- A bounded driver advances the physical programme between service attempts;
its next quote is regenerated from that actual last cache. -/
def run (state : Paid.State model domain original baseline actualHorizon) : Nat → Paid.State model domain original baseline actualHorizon
  | 0 => state
  | fuel+1 => run (Round.next state reader unit point rival) fuel

def executed (state : Paid.State model domain original baseline actualHorizon) : Nat → List (Prefix.Rule model.source.code)
  | 0 => []
  | fuel+1 => Round.stages state reader unit point rival ++ executed (Round.next state reader unit point rival) fuel

structure Entry where
  before : Paid.State model domain original baseline actualHorizon
  event : Paid.Turn (Round.prepared before) reader (Round.quoted before unit) point rival
  generated : event = Round.service before reader unit point rival

def audit (state : Paid.State model domain original baseline actualHorizon) : Nat → List (Entry (domain := domain) (original := original) (baseline := baseline) (actualHorizon := actualHorizon) reader unit point rival)
  | 0 => []
  | fuel+1 => ⟨state,Round.service state reader unit point rival,rfl⟩ ::
      audit (Round.next state reader unit point rival) fuel

def paidCount (state : Paid.State model domain original baseline actualHorizon) : Nat → Nat
  | 0 => 0
  | fuel+1 => (if (Round.service state reader unit point rival).learned then 1 else 0) +
      paidCount (Round.next state reader unit point rival) fuel

variable (fuel : Nat)

theorem no_old_or_new_actual_stage_is_replayed_or_erased :
    (run reader unit point rival state fuel).past = state.past ++ executed reader unit point rival state fuel := by
  induction fuel generalizing state with
  | zero => exact (List.append_nil _).symm
  | succ fuel ih =>
      change (run reader unit point rival (Round.next state reader unit point rival) fuel).past = _
      rw [ih,Round.every_attempt_and_executed_learning_stage_is_locked_into_past,List.append_assoc]
      rfl

theorem every_finite_feedback_chain_keeps_actual_local_knowledge
    (covered : Knowledge.Contains state.beliefs (state.current point rival)) :
    Knowledge.Contains (run reader unit point rival state fuel).beliefs
      ((run reader unit point rival state fuel).current point rival) := by
  induction fuel generalizing state with
  | zero => exact covered
  | succ fuel ih => exact ih _ (Round.actual_origin_knowledge_survives_both_phases _ _ _ _ _ covered)

theorem the_driver_is_the_actual_execution_of_its_generated_rules :
    (run reader unit point rival state fuel).current point rival =
      Window.Observed.Transcript.actualView (executed reader unit point rival state fuel) (state.current point rival) rival := by
  change Window.Observed.Transcript.actualView _ point rival = _
  rw [no_old_or_new_actual_stage_is_replayed_or_erased]
  unfold Window.Observed.Transcript.actualView
  rw [List.foldl_append]
  rfl

theorem every_round_reuses_the_actual_last_cache_and_current (later : Nat) :
    run reader unit point rival state (fuel+later) =
      run reader unit point rival (run reader unit point rival state fuel) later := by
  induction fuel generalizing state with
  | zero => rw [Nat.zero_add];rfl
  | succ fuel ih =>
      rw [Nat.succ_add]
      change run reader unit point rival (Round.next state reader unit point rival) (fuel+later) = _
      exact ih _

theorem every_audited_attempt_comes_from_its_own_actual_prior_round
    (entry : Entry (domain := domain) (original := original) (baseline := baseline) (actualHorizon := actualHorizon) reader unit point rival)
    (present : entry ∈ audit reader unit point rival state fuel) :
    ∃ offset < fuel, entry.before = run reader unit point rival state offset := by
  induction fuel generalizing state with
  | zero => cases present
  | succ fuel ih =>
      change entry ∈ _ :: _ at present
      rcases List.mem_cons.mp present with first | rest
      · subst entry
        exact ⟨0,Nat.zero_lt_succ _,rfl⟩
      · obtain ⟨offset,bound,same⟩ := ih (Round.next state reader unit point rival) rest
        exact ⟨offset+1,Nat.succ_lt_succ bound,same⟩

theorem each_audited_learning_attempt_owns_a_fresh_charge_at_its_actual_cut
    (entry : Entry (domain := domain) (original := original) (baseline := baseline) (actualHorizon := actualHorizon) reader unit point rival)
    (present : entry ∈ audit reader unit point rival state fuel)
    (paid : entry.event.learned = true) :
    ∃ offset < fuel, entry.before = run reader unit point rival state offset ∧
      Charge.paid (Round.quoted entry.before unit) model reader (entry.before.current point rival) rival
        (Charge.endAt (Round.quoted entry.before unit) model reader (entry.before.current point rival) rival) := by
  obtain ⟨offset,bound,same⟩ := every_audited_attempt_comes_from_its_own_actual_prior_round state reader unit point rival fuel entry present
  have charged := Paid.Turn.each_learning_turn_releases_a_fresh_source_indexed_charge entry.event paid
  exact ⟨offset,bound,same,charged⟩

abbrev remaining (state : Paid.State model domain original baseline actualHorizon) :=
  min actualHorizon (horizon domain) - state.past.length

theorem every_live_round_reduces_the_actual_unconsumed_window :
    remaining (Round.next state reader unit point rival) ≤ remaining state - 1 := by
  by_cases live : Progress.Live state
  · have progress := Round.each_live_round_has_actual_progress state reader unit point rival live
    unfold remaining
    omega
  · have retained := congrArg List.length (Round.every_attempt_and_executed_learning_stage_is_locked_into_past state reader unit point rival)
    simp only [List.length_append] at retained
    have domainBound := state.within
    have actualBound := state.actualWithin
    unfold Progress.Live at live
    unfold remaining
    simp only [Nat.min_def]
    split <;> omega

theorem sufficient_rounds_exhaust_the_common_physical_window :
    remaining (run reader unit point rival state fuel) ≤ remaining state - fuel := by
  induction fuel generalizing state with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      have tail := ih (Round.next state reader unit point rival)
      have step := every_live_round_reduces_the_actual_unconsumed_window state reader unit point rival
      change remaining (run reader unit point rival (Round.next state reader unit point rival) fuel) ≤ _
      omega

theorem no_unreserved_service_can_force_an_empty_physical_spin
    (enough : remaining state ≤ fuel) :
    remaining (run reader unit point rival state fuel) = 0 := by
  have bound := sufficient_rounds_exhaust_the_common_physical_window state reader unit point rival fuel
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving
