import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IntentServiceRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BatchReentry

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

abbrev Stages := LocalJointResponse.Stages model
abbrev fuel := LocalJointResponse.fuel model start
abbrev service (past : Stages model) := IntentServiceRun.produce vocabulary encoding law start past (OriginQueue.environment start)

-- Each batch takes its own entering snapshot. A completed old batch cannot
-- discharge a response first learned at an actual successor cut.
def idle (past : Stages model) : Prop :=
  ∀ site, RetainedIntent.intent vocabulary encoding law start past site = []
instance (past : Stages model) : Decidable (idle model start vocabulary encoding law past) := by
  unfold idle; infer_instance

def Clear (past : Stages model) : Prop :=
  LocalJointResponse.Clear model start vocabulary encoding law past ∧ idle model start vocabulary encoding law past
instance (past : Stages model) : Decidable (Clear model start vocabulary encoding law past) := by
  unfold Clear; infer_instance

theorem a_nonempty_serviced_batch_spends_actual_fuel (past : Stages model)
    (needed : ¬ idle model start vocabulary encoding law past)
    (serviced : (service model start vocabulary encoding law past).status = .serviced) :
    fuel model start (service model start vocabulary encoding law past).stages < fuel model start past := by
  have existsSite : ∃ site, RetainedIntent.intent vocabulary encoding law start past site ≠ [] := by
    simpa only [idle, not_forall] using needed
  obtain ⟨site, nonempty⟩ := existsSite
  obtain ⟨index, bounded, _⟩ := IntentServiceRun.every_entry_intent_has_an_actual_nonempty_submission_before_the_deadline
    vocabulary encoding law start past (OriginQueue.environment start) serviced site nonempty
  have clocks := IntentServiceRun.the_generated_service_time_spends_exactly_its_source_budget
    vocabulary encoding law start past (OriginQueue.environment start) serviced
  have clock : fuel model start (service model start vocabulary encoding law past).stages =
      fuel model start past - IntentServiceRun.used vocabulary encoding law start past (OriginQueue.environment start) := clocks.2.2
  have live : 0 < fuel model start past := by
    have ready := IntentServiceRun.generated_used_is_bounded vocabulary encoding law start past (OriginQueue.environment start)
    change _ ≤ min _ (fuel model start past) at ready
    have := ready.trans (min_le_right _ _)
    omega
  omega

inductive Action (past : Stages model) where
  | batch (needed : ¬ idle model start vocabulary encoding law past)
      (serviced : (service model start vocabulary encoding law past).status = .serviced)
  | native (action : LocalJointResponse.Action model start vocabulary encoding law past)

def after (past : Stages model) : Action model start vocabulary encoding law past → Stages model
  | .batch _ _ => (service model start vocabulary encoding law past).stages
  | .native action => LocalJointResponse.after model start vocabulary encoding law past action

inductive Step (past : Stages model) where
  | complete (covered : Clear model start vocabulary encoding law past)
  | exhausted (empty : fuel model start past = 0) (unclosed : ¬ Clear model start vocabulary encoding law past)
  | refused (needed : ¬ idle model start vocabulary encoding law past)
      (failed : (service model start vocabulary encoding law past).status ≠ .serviced)
  | advance (action : Action model start vocabulary encoding law past)

def step (past : Stages model) : Step model start vocabulary encoding law past :=
  if empty : idle model start vocabulary encoding law past then
    if native : LocalJointResponse.Clear model start vocabulary encoding law past then .complete ⟨native, empty⟩
    else if live : 0 < fuel model start past then
      match LocalJointResponse.step model start vocabulary encoding law past with
      | .advance action => .advance (.native action)
      | .clear covered => False.elim (native covered)
      | .exhausted stopped => False.elim (by change fuel model start past = 0 at stopped; omega)
    else .exhausted (by omega) (fun covered => native covered.1)
  else if live : 0 < fuel model start past then
    if serviced : (service model start vocabulary encoding law past).status = .serviced then
      .advance (.batch empty serviced)
    else .refused empty serviced
  else .exhausted (by omega) (fun covered => empty covered.2)

theorem every_action_keeps_the_actual_prefix (past : Stages model)
    (action : Action model start vocabulary encoding law past) :
    past <+: after model start vocabulary encoding law past action := by
  cases action with
  | batch _ _ => exact IntentServiceRun.every_result_keeps_the_whole_original_prefix _ _ _ _ _ _
  | native action => exact LocalJointResponse.every_action_retains_the_whole_actual_prefix _ _ _ _ _ _ action

theorem every_action_spends_actual_fuel (past : Stages model)
    (action : Action model start vocabulary encoding law past) :
    fuel model start (after model start vocabulary encoding law past action) < fuel model start past := by
  cases action with
  | batch needed serviced => exact a_nonempty_serviced_batch_spends_actual_fuel _ _ _ _ _ _ needed serviced
  | native action => exact LocalJointResponse.every_action_spends_actual_fuel _ _ _ _ _ _ action

inductive Status where
  | jointComplete | exhausted | serviceRefused (reason : IntentServiceRun.Status) | observationCut
  deriving DecidableEq

structure Result where
  stages : Stages model
  status : Status
  batches : List (Stages model)

def run : Nat → Stages model → Result model
  | 0, past =>
    if Clear model start vocabulary encoding law past then ⟨past, .jointComplete, []⟩
    else if fuel model start past = 0 then ⟨past, .exhausted, []⟩
    else ⟨past, .observationCut, []⟩
  | rounds + 1, past => match step model start vocabulary encoding law past with
    | .complete _ => ⟨past, .jointComplete, []⟩
    | .exhausted _ _ => ⟨past, .exhausted, []⟩
    | .refused _ _ => ⟨(service model start vocabulary encoding law past).stages,
        .serviceRefused (service model start vocabulary encoding law past).status, [past]⟩
    | .advance action =>
      let next := run rounds (after model start vocabulary encoding law past action)
      ⟨next.stages, next.status, match action with
        | .batch _ _ => past :: next.batches
        | .native _ => next.batches⟩

def produce (past : Stages model) := run model start vocabulary encoding law (fuel model start past) past

theorem every_run_keeps_the_whole_history (rounds : Nat) (past : Stages model) :
    past <+: (run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run]; split <;> first | exact List.prefix_refl _ | split <;> exact List.prefix_refl _
  | succ rounds ih =>
    cases chosen : step model start vocabulary encoding law past <;> simp only [run, chosen]
    · exact List.prefix_refl _
    · exact List.prefix_refl _
    · exact IntentServiceRun.every_result_keeps_the_whole_original_prefix _ _ _ _ _ _
    · exact (every_action_keeps_the_actual_prefix _ _ _ _ _ _ _).trans (ih _)

-- This includes the failed batch's actually executed partial prefix.
theorem every_recorded_batch_is_executed_in_the_final_history (rounds : Nat) (past entry : Stages model)
    (recorded : entry ∈ (run model start vocabulary encoding law rounds past).batches) :
    past <+: entry ∧ (service model start vocabulary encoding law entry).stages <+:
      (run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero =>
    simp only [run] at recorded
    split_ifs at recorded
    all_goals simp_all
  | succ rounds ih =>
    cases chosen : step model start vocabulary encoding law past <;> simp only [run, chosen] at recorded ⊢
    · contradiction
    · contradiction
    · have same : entry = past := by simpa using recorded
      subst entry
      exact ⟨List.prefix_refl _, List.prefix_refl _⟩
    · rename_i action
      cases action with
      | batch needed serviced =>
        rcases List.mem_cons.mp recorded with same | later
        · subst entry
          exact ⟨List.prefix_refl _, every_run_keeps_the_whole_history _ _ _ _ _ _ _⟩
        · have found := ih _ later
          exact ⟨(every_action_keeps_the_actual_prefix _ _ _ _ _ _ (.batch needed serviced)).trans found.1, found.2⟩
      | native action =>
        have found := ih _ recorded
        exact ⟨(LocalJointResponse.every_action_retains_the_whole_actual_prefix _ _ _ _ _ _ action).trans found.1, found.2⟩

theorem completion_consumes_the_newest_same_cut_gates (rounds : Nat) (past : Stages model)
    (complete : (run model start vocabulary encoding law rounds past).status = .jointComplete) :
    Clear model start vocabulary encoding law (run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run] at complete ⊢; (split_ifs at complete ⊢; simp_all)
  | succ rounds ih =>
    cases chosen : step model start vocabulary encoding law past <;>
      simp only [run, chosen] at complete ⊢ <;> try contradiction
    · assumption
    · exact ih _ complete

theorem a_source_budget_never_returns_an_observation_cut (rounds : Nat) (past : Stages model)
    (bounded : fuel model start past ≤ rounds) :
    (run model start vocabulary encoding law rounds past).status ≠ .observationCut := by
  induction rounds generalizing past with
  | zero => simp only [run]; split_ifs <;> simp_all
  | succ rounds ih =>
    cases chosen : step model start vocabulary encoding law past <;> simp only [run, chosen] <;> try simp
    rename_i action
    have spent := every_action_spends_actual_fuel model start vocabulary encoding law past action
    exact ih _ (by omega)

theorem exhaustion_keeps_zero_fuel_and_an_unclosed_current_gate (rounds : Nat) (past : Stages model)
    (stopped : (run model start vocabulary encoding law rounds past).status = .exhausted) :
    fuel model start (run model start vocabulary encoding law rounds past).stages = 0 ∧
      ¬ Clear model start vocabulary encoding law (run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [run] at stopped ⊢; (split_ifs at stopped ⊢; simp_all)
  | succ rounds ih =>
    cases chosen : step model start vocabulary encoding law past <;> simp only [run, chosen] at stopped ⊢ <;> try contradiction
    · exact ⟨by assumption, by assumption⟩
    · exact ih _ stopped

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BatchReentry
