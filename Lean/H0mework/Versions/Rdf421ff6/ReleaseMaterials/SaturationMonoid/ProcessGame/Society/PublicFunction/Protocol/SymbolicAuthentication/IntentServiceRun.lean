import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IntentServiceProgress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IntentServiceRun

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (rival : Opponent code)

abbrev horizon := ServiceClock.horizon (RetainedIntent.origin start past)
abbrev limit := min (horizon start past) (EventStep.seed (RetainedIntent.origin start past)).remaining
abbrev current (n : Nat) := IntentServiceProgress.cursorAt vocabulary encoding law start past rival n

def closed (n : Nat) : Bool := (List.finRange code.sites).all fun site => decide
  (RetainedIntent.work vocabulary encoding law start past site ((EventStep.seed (current vocabulary encoding law start past rival n)).frame.inbox site) = [])

-- find? stops at the first closed actual prefix. A missing closing prefix keeps
-- the real partially executed history and is reported as budget exhaustion.
def stopping : Option Nat := (List.range (limit start past + 1)).find? (closed vocabulary encoding law start past rival)
def used : Nat := (stopping vocabulary encoding law start past rival).getD (limit start past)
def suffix := List.replicate (used vocabulary encoding law start past rival) (RetainedIntent.protocol vocabulary encoding law start past, rival)

inductive Status where
  | serviced | nonabsorbingSource | activationUnavailable | readingUnstable | insufficientBudget
  deriving DecidableEq

structure Result (code : Code Party Good Port (Mandate.State Party Technology) Instrument) where
  stages : List (EventHistory.Stage (code := code))
  status : Status

-- The time budget comes from the original roster and actual remaining fuel.
def produce : Result code :=
  if SourceResponseCapacity.inspect code = true then
    if RetainedIntent.activationCheck vocabulary encoding law start past = true then
      if RetainedIntent.deliveryCheck vocabulary encoding law start past = true then
        ⟨past ++ suffix vocabulary encoding law start past rival,
          if (stopping vocabulary encoding law start past rival).isSome then .serviced else .insufficientBudget⟩
      else ⟨past, .readingUnstable⟩
    else ⟨past, .activationUnavailable⟩
  else ⟨past, .nonabsorbingSource⟩

theorem every_result_keeps_the_whole_original_prefix :
    past <+: (produce vocabulary encoding law start past rival).stages := by
  unfold produce
  split <;> try exact List.prefix_refl _
  split <;> try exact List.prefix_refl _
  split
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

theorem service_facts (serviced : (produce vocabulary encoding law start past rival).status = .serviced) :
    RetainedIntent.inspect vocabulary encoding law start past = true ∧
    closed vocabulary encoding law start past rival (used vocabulary encoding law start past rival) = true ∧
    (produce vocabulary encoding law start past rival).stages = past ++ suffix vocabulary encoding law start past rival := by
  by_cases absorption : SourceResponseCapacity.inspect code = true
  · by_cases activation : RetainedIntent.activationCheck vocabulary encoding law start past = true
    · by_cases delivery : RetainedIntent.deliveryCheck vocabulary encoding law start past = true
      · have status : (if (stopping vocabulary encoding law start past rival).isSome then Status.serviced else .insufficientBudget) = .serviced := by
          simpa only [produce, if_pos absorption, if_pos activation, if_pos delivery] using serviced
        have found : (stopping vocabulary encoding law start past rival).isSome = true := by
          by_cases present : (stopping vocabulary encoding law start past rival).isSome = true
          · exact present
          · simp only [if_neg present] at status
            contradiction
        refine ⟨by simp [RetainedIntent.inspect, absorption, activation, delivery], ?_, ?_⟩
        · cases actual : stopping vocabulary encoding law start past rival with
          | none => rw [actual] at found; contradiction
          | some index =>
            have closes := List.find?_some actual
            simpa only [used, actual, Option.getD_some] using closes
        · simp only [produce, if_pos absorption, if_pos activation, if_pos delivery]
      · simp only [produce, if_pos absorption, if_pos activation, if_neg delivery] at serviced
        contradiction
    · simp only [produce, if_pos absorption, if_neg activation] at serviced
      contradiction
  · simp only [produce, if_neg absorption] at serviced
    contradiction

theorem generated_used_is_bounded : used vocabulary encoding law start past rival ≤ limit start past := by
  cases actual : stopping vocabulary encoding law start past rival with
  | none => simp only [used, actual, Option.getD_none, le_refl]
  | some index =>
    have member := List.mem_of_find?_eq_some actual
    have bounded := List.mem_range.mp member
    simp only [used, actual, Option.getD_some]
    omega

theorem the_source_budget_guarantees_service
    (accepted : RetainedIntent.inspect vocabulary encoding law start past = true)
    (budget : horizon start past ≤ (EventStep.seed (RetainedIntent.origin start past)).remaining) :
    (produce vocabulary encoding law start past rival).status = .serviced := by
  have checks : SourceResponseCapacity.inspect code = true ∧ RetainedIntent.activationCheck vocabulary encoding law start past = true ∧
      RetainedIntent.deliveryCheck vocabulary encoding law start past = true := by simpa [RetainedIntent.inspect, and_assoc] using accepted
  have cutoff : limit start past = horizon start past := min_eq_left budget
  have endClosed : closed vocabulary encoding law start past rival (horizon start past) = true := by
    apply List.all_eq_true.mpr
    intro site _
    exact decide_eq_true (IntentServiceProgress.the_generated_window_closes_every_retained_intent
      vocabulary encoding law start past rival accepted budget site)
  have found : (stopping vocabulary encoding law start past rival).isSome = true := by
    cases actual : stopping vocabulary encoding law start past rival with
    | some index => rfl
    | none =>
      have missing := List.find?_eq_none.mp actual (horizon start past) (by rw [cutoff]; exact List.mem_range.mpr (by omega))
      rw [endClosed] at missing
      contradiction
  simp only [produce, checks.1, checks.2.1, checks.2.2, if_true, found]

theorem generated_execution_is_the_actual_roster_cursor
    (serviced : (produce vocabulary encoding law start past rival).status = .serviced) :
    EventHistory.execute start (produce vocabulary encoding law start past rival).stages =
      current vocabulary encoding law start past rival (used vocabulary encoding law start past rival) := by
  rw [(service_facts vocabulary encoding law start past rival serviced).2.2, StageQueue.execute_append]
  exact ServiceClock.installed_stages_are_the_actual_service_cursor _ _ _ _

theorem the_generated_service_time_spends_exactly_its_source_budget
    (serviced : (produce vocabulary encoding law start past rival).status = .serviced) :
    (produce vocabulary encoding law start past rival).stages.length = past.length + used vocabulary encoding law start past rival ∧
    used vocabulary encoding law start past rival ≤ horizon start past ∧
    (EventStep.seed (EventHistory.execute start (produce vocabulary encoding law start past rival).stages)).remaining =
      (EventStep.seed (RetainedIntent.origin start past)).remaining - used vocabulary encoding law start past rival := by
  refine ⟨?_, (generated_used_is_bounded vocabulary encoding law start past rival).trans (min_le_left _ _), ?_⟩
  · rw [(service_facts vocabulary encoding law start past rival serviced).2.2]
    simp [suffix]
  · rw [generated_execution_is_the_actual_roster_cursor vocabulary encoding law start past rival serviced]
    exact (ServiceClock.clocks _ _ _ _).2.1

theorem every_retained_local_intent_is_closed_at_the_generated_end
    (serviced : (produce vocabulary encoding law start past rival).status = .serviced) (site : Fin code.sites) :
    RetainedIntent.work vocabulary encoding law start past site
      ((EventStep.seed (EventHistory.execute start (produce vocabulary encoding law start past rival).stages)).frame.inbox site) = [] := by
  rw [generated_execution_is_the_actual_roster_cursor vocabulary encoding law start past rival serviced]
  exact of_decide_eq_true ((List.all_eq_true.mp (service_facts vocabulary encoding law start past rival serviced).2.1)
    site (List.mem_finRange _))

theorem every_entry_intent_has_an_actual_nonempty_submission_before_the_deadline
    (serviced : (produce vocabulary encoding law start past rival).status = .serviced)
    (site : Fin code.sites) (needed : RetainedIntent.intent vocabulary encoding law start past site ≠ []) :
    ∃ index < used vocabulary encoding law start past rival,
      StageTrace.activation (IntentServiceProgress.row vocabulary encoding law start past rival index) = some site ∧
      (IntentServiceProgress.row vocabulary encoding law start past rival index).submitted = RetainedIntent.intent vocabulary encoding law start past site ∧
      ResponseCapacity.productive (current vocabulary encoding law start past rival index)
        (RetainedIntent.protocol vocabulary encoding law start past) rival = true ∧
      ResponseCapacity.rank (current vocabulary encoding law start past rival (index + 1)) <
        ResponseCapacity.rank (current vocabulary encoding law start past rival index) := by
  have checks := service_facts vocabulary encoding law start past rival serviced
  have closedSite := of_decide_eq_true ((List.all_eq_true.mp checks.2.1) site (List.mem_finRange _))
  obtain ⟨index, bounded, owned⟩ : ∃ index < used vocabulary encoding law start past rival,
      StageTrace.activation (IntentServiceProgress.row vocabulary encoding law start past rival index) = some site := by
    rcases IntentServiceProgress.every_initial_intent_is_served_or_still_locally_present vocabulary encoding law start past rival
      checks.1 site needed (used vocabulary encoding law start past rival) with served | unchanged
    · exact served
    · rw [unchanged] at closedSite
      simp only [RetainedIntent.work, if_true] at closedSite
      exact False.elim (needed closedSite)
  have submission := RetainedIntent.an_owned_service_submits_the_nonempty_entry_intent vocabulary encoding law start past
    (current vocabulary encoding law start past rival index) rival site owned
  have productive : ResponseCapacity.productive (current vocabulary encoding law start past rival index)
      (RetainedIntent.protocol vocabulary encoding law start past) rival = true := by
    simp only [ResponseCapacity.productive, owned, Option.isSome_some, Bool.true_and]
    rw [submission.1]
    simpa using submission.2
  exact ⟨index, bounded, owned, submission.1, productive,
    ResponseCapacity.a_nonempty_owned_action_strictly_spends_capacity
      (RetainedIntent.source_checks vocabulary encoding law start past checks.1).1 _ _ _ productive⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IntentServiceRun
