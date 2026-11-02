import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueuedContinuationRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResponseSweep

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev Stages := List (EventHistory.Stage (code := model.source.code))
def fuelAt (past : Stages model) := (EventStep.seed (EventHistory.execute start past)).remaining

def unhandled (past : Stages model) :=
  (StageAccountability.ledger start vocabulary encoding law past).filter fun incident =>
    decide (IncidentResponse.identity model start vocabulary encoding law incident ∉
      (IncidentResponse.journal model start past vocabulary encoding law).map
        (IncidentResponse.Answer.id model start vocabulary encoding law))

abbrev arrival (past : Stages model) := QueuedContinuation.waiting model start past vocabulary encoding law
abbrev enough (past : Stages model) :=
  QueuedContinuation.duration model start past vocabulary encoding law < (EventStep.seed (EventHistory.execute start past)).remaining

inductive Step (past : Stages model) where
  | windowExhausted (denied : ¬ enough model start vocabulary encoding law past)
  | complete (fuel : enough model start vocabulary encoding law past)
      (covered : unhandled model start vocabulary encoding law (arrival model start vocabulary encoding law past) = [])
  | idle (fuel : enough model start vocabulary encoding law past)
      (actual : IncidentResponse.produce model start (arrival model start vocabulary encoding law past) vocabulary encoding law = .idle)
  | awaitingReview (fuel : enough model start vocabulary encoding law past)
      (actual : IncidentResponse.produce model start (arrival model start vocabulary encoding law past) vocabulary encoding law = .awaitingReview)
  | blocked (fuel : enough model start vocabulary encoding law past) (reason : IncidentResponse.Obstruction)
      (actual : IncidentResponse.produce model start (arrival model start vocabulary encoding law past) vocabulary encoding law = .blocked reason)
  | advance (fuel : enough model start vocabulary encoding law past)
      (response : IncidentResponse.Ready model start (arrival model start vocabulary encoding law past) vocabulary encoding law)
      (actual : IncidentResponse.produce model start (arrival model start vocabulary encoding law past) vocabulary encoding law = .ready response)

def step (past : Stages model) : Step model start vocabulary encoding law past :=
  if fuel : enough model start vocabulary encoding law past then
    if covered : unhandled model start vocabulary encoding law (arrival model start vocabulary encoding law past) = [] then
      .complete fuel covered
    else match actual : IncidentResponse.produce model start (arrival model start vocabulary encoding law past) vocabulary encoding law with
      | .idle => .idle fuel actual
      | .awaitingReview => .awaitingReview fuel actual
      | .blocked reason => .blocked fuel reason actual
      | .ready response => .advance fuel response actual
  else .windowExhausted fuel

def appended (past : Stages model)
    (response : IncidentResponse.Ready model start (arrival model start vocabulary encoding law past) vocabulary encoding law) :=
  arrival model start vocabulary encoding law past ++
    [(IncidentResponse.protocol model start (arrival model start vocabulary encoding law past) vocabulary encoding law response, OriginQueue.environment start)]

inductive Status where
  | complete | iterationExhausted | windowExhausted | idle | awaitingReview
  | blocked (reason : IncidentResponse.Obstruction)
  deriving DecidableEq

structure Result where
  stages : Stages model
  status : Status

def run : Nat → Stages model → Result model
  | 0, past => ⟨past, .iterationExhausted⟩
  | rounds + 1, past => match step model start vocabulary encoding law past with
    | .windowExhausted _ => ⟨past, .windowExhausted⟩
    | .complete _ _ => ⟨arrival model start vocabulary encoding law past, .complete⟩
    | .idle _ _ => ⟨arrival model start vocabulary encoding law past, .idle⟩
    | .awaitingReview _ _ => ⟨arrival model start vocabulary encoding law past, .awaitingReview⟩
    | .blocked _ reason _ => ⟨arrival model start vocabulary encoding law past, .blocked reason⟩
    | .advance _ response _ => run rounds (appended model start vocabulary encoding law past response)

def produce (past : Stages model) :=
  run model start vocabulary encoding law (EventStep.seed (EventHistory.execute start past)).remaining past

theorem arrival_retains_the_actual_prefix (past : Stages model) :
    past <+: arrival model start vocabulary encoding law past := by
  unfold arrival QueuedContinuation.waiting
  split
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

theorem every_run_retains_the_entire_original_history (rounds : Nat) (past : Stages model) :
    past <+: (run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero => exact List.prefix_refl _
  | succ rounds ih =>
    simp only [run]
    split
    · exact List.prefix_refl _
    · exact arrival_retains_the_actual_prefix model start vocabulary encoding law past
    · exact arrival_retains_the_actual_prefix model start vocabulary encoding law past
    · exact arrival_retains_the_actual_prefix model start vocabulary encoding law past
    · exact arrival_retains_the_actual_prefix model start vocabulary encoding law past
    · exact ((arrival_retains_the_actual_prefix model start vocabulary encoding law past).trans
        (List.prefix_append _ _)).trans (ih _)

theorem the_original_journal_and_incident_ledger_are_retained (past : Stages model) :
    IncidentResponse.journal model start past vocabulary encoding law <+:
        IncidentResponse.journal model start (produce model start vocabulary encoding law past).stages vocabulary encoding law ∧
      StageAccountability.ledger start vocabulary encoding law past <+:
        StageAccountability.ledger start vocabulary encoding law (produce model start vocabulary encoding law past).stages := by
  obtain ⟨more, same⟩ := every_run_retains_the_entire_original_history model start vocabulary encoding law
    (EventStep.seed (EventHistory.execute start past)).remaining past
  change past ++ more = (produce model start vocabulary encoding law past).stages at same
  rw [← same]
  refine ⟨IncidentResponse.Prefix.journal_is_an_actual_prefix model start vocabulary encoding law past more, ?_⟩
  rw [StageAccountability.ledger_extends_by_its_generated_next]
  exact List.prefix_append _ _

theorem completed_run_covers_every_actual_incident (rounds : Nat) (past : Stages model)
    (completed : (run model start vocabulary encoding law rounds past).status = .complete) :
    ∀ incident ∈ StageAccountability.ledger start vocabulary encoding law (run model start vocabulary encoding law rounds past).stages,
      IncidentResponse.identity model start vocabulary encoding law incident ∈
        (IncidentResponse.journal model start (run model start vocabulary encoding law rounds past).stages vocabulary encoding law).map
          (IncidentResponse.Answer.id model start vocabulary encoding law) := by
  induction rounds generalizing past with
  | zero => cases completed
  | succ rounds ih =>
    cases observed : step model start vocabulary encoding law past <;>
      simp only [run, observed] at completed ⊢ <;> try contradiction
    · rename_i fuel covered
      intro incident inside
      by_contra missing
      have member : incident ∈ unhandled model start vocabulary encoding law (arrival model start vocabulary encoding law past) :=
        List.mem_filter.mpr ⟨inside, decide_eq_true missing⟩
      rw [covered] at member
      exact List.not_mem_nil member
    · exact ih _ completed

theorem a_response_step_registers_exactly_one_fresh_original_identity (past : Stages model)
    (response : IncidentResponse.Ready model start (arrival model start vocabulary encoding law past) vocabulary encoding law)
    (actual : IncidentResponse.produce model start (arrival model start vocabulary encoding law past) vocabulary encoding law = .ready response) :
    (IncidentResponse.journal model start (appended model start vocabulary encoding law past response) vocabulary encoding law).map
        (IncidentResponse.Answer.id model start vocabulary encoding law) =
      (IncidentResponse.journal model start (arrival model start vocabulary encoding law past) vocabulary encoding law).map
        (IncidentResponse.Answer.id model start vocabulary encoding law) ++ [IncidentResponse.identity model start vocabulary encoding law response.incident] ∧
    IncidentResponse.identity model start vocabulary encoding law response.incident ∉
      (IncidentResponse.journal model start (arrival model start vocabulary encoding law past) vocabulary encoding law).map
        (IncidentResponse.Answer.id model start vocabulary encoding law) :=
  ⟨IncidentResponse.a_generated_response_is_registered_once model start _ vocabulary encoding law response (OriginQueue.environment start) actual,
    IncidentResponse.a_ready_response_has_not_been_registered model start _ vocabulary encoding law response actual⟩

theorem a_response_step_consumes_actual_fuel (past : Stages model)
    (fuel : enough model start vocabulary encoding law past)
    (response : IncidentResponse.Ready model start (arrival model start vocabulary encoding law past) vocabulary encoding law) :
    (EventStep.seed (EventHistory.execute start (appended model start vocabulary encoding law past response))).remaining <
      (EventStep.seed (EventHistory.execute start past)).remaining := by
  have clock := (OriginQueue.clocks_and_roster start (EventHistory.execute start past)
    (QueuedContinuation.protocols model) (QueuedContinuation.duration model start past vocabulary encoding law)).2.1
  have waiting := QueuedContinuation.waiting_is_the_actual_source_queue_prefix model start past vocabulary encoding law fuel
  unfold appended
  rw [OriginQueue.execute_append]
  change (EventStep.seed ((EventHistory.execute start (arrival model start vocabulary encoding law past)).after _ _)).remaining < _
  rw [EventStep.actual_next_state]
  change (EventStep.seed (EventHistory.execute start (arrival model start vocabulary encoding law past))).remaining - 1 < _
  rw [waiting, clock]
  unfold enough at fuel
  omega

theorem an_iteration_cut_from_the_source_budget_has_no_actual_fuel
    (rounds : Nat) (past : Stages model)
    (bounded : (EventStep.seed (EventHistory.execute start past)).remaining ≤ rounds)
    (cut : (run model start vocabulary encoding law rounds past).status = .iterationExhausted) :
    (EventStep.seed (EventHistory.execute start (run model start vocabulary encoding law rounds past).stages)).remaining = 0 := by
  change fuelAt model start past ≤ rounds at bounded
  change fuelAt model start (run model start vocabulary encoding law rounds past).stages = 0
  induction rounds generalizing past with
  | zero => exact Nat.eq_zero_of_le_zero bounded
  | succ rounds ih =>
    cases observed : step model start vocabulary encoding law past <;>
      simp only [run, observed] at cut ⊢ <;> try contradiction
    rename_i fuel response actual
    have spent := a_response_step_consumes_actual_fuel model start vocabulary encoding law past fuel response
    change fuelAt model start (appended model start vocabulary encoding law past response) < fuelAt model start past at spent
    apply ih (appended model start vocabulary encoding law past response) <;> first | exact cut | omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResponseSweep
