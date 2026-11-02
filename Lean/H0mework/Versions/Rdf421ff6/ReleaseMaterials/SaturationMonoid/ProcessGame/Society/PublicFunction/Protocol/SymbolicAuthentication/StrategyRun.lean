import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StrategyPlan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StrategyRun

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open StrategyPlan

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (allowance : Nat)

-- Evaluate the retained receipt gate first; the public completion proposition is unchanged.
def Ready (state : State model) : Prop :=
  InterferenceValidity.closed model start vocabulary encoding law state ∧
    BatchReentry.idle model start vocabulary encoding law state.past ∧
    LocalJointResponse.Clear model start vocabulary encoding law state.past
instance (state : State model) : Decidable (Ready model start vocabulary encoding law state) := by
  unfold Ready; infer_instance

-- Existential source actions, universal admitted communication at every cut.
def guarantees : Nat → State model → Bool
  | 0, state => decide (Ready model start vocabulary encoding law state)
  | rounds + 1, state =>
    if Ready model start vocabulary encoding law state then true
    else if CompletionState.fuel model start state = 0 then false
    else (prepare model start vocabulary encoding law state).any fun plan =>
      (InterferenceEnvelope.choices start state.past allowance).all fun move =>
        guarantees rounds (after model start vocabulary encoding law state plan move)

def select (rounds : Nat) (state : State model) :=
  (prepare model start vocabulary encoding law state).find? fun plan =>
    (InterferenceEnvelope.choices start state.past allowance).all fun move =>
      guarantees model start vocabulary encoding law allowance rounds (after model start vocabulary encoding law state plan move)

-- A selected segment commits its literal tail. Re-solving that tail would
-- repeat the same finite search at every physical cut.
def continuation (rounds : Nat) (state : State model) : Option (Plan model start vocabulary encoding law state) :=
  match pending : state.todo with
  | head :: tail => some (.queued head tail pending)
  | [] => select model start vocabulary encoding law allowance rounds state

theorem selected_plan_is_source_generated (rounds : Nat) (state : State model)
    (plan : Plan model start vocabulary encoding law state)
    (chosen : select model start vocabulary encoding law allowance rounds state = some plan) :
    plan ∈ prepare model start vocabulary encoding law state := List.mem_of_find?_eq_some chosen

theorem an_accepted_selection_is_the_actual_continuation (rounds : Nat) (state : State model)
    (plan : Plan model start vocabulary encoding law state)
    (chosen : select model start vocabulary encoding law allowance rounds state = some plan) :
    continuation model start vocabulary encoding law allowance rounds state = some plan := by
  have generated := selected_plan_is_source_generated model start vocabulary encoding law allowance rounds state plan chosen
  unfold continuation
  split
  · rename_i head tail pending
    unfold prepare at generated
    split at generated
    · rename_i first rest actual
      obtain ⟨rfl, rfl⟩ := List.cons.inj (actual.symm.trans pending)
      have same := List.mem_singleton.mp generated
      subst plan
      rfl
    · rename_i absent
      have impossible : [] = head :: tail := absent.symm.trans pending
      cases impossible
  · exact chosen

theorem a_selected_plan_handles_every_generated_move (rounds : Nat) (state : State model)
    (plan : Plan model start vocabulary encoding law state)
    (chosen : select model start vocabulary encoding law allowance rounds state = some plan)
    (move : Move model.source.code) (inside : move ∈ InterferenceEnvelope.choices start state.past allowance) :
    guarantees model start vocabulary encoding law allowance rounds (after model start vocabulary encoding law state plan move) = true :=
  by
    unfold select at chosen
    have supported := List.find?_some chosen
    exact List.all_eq_true.mp supported move inside

theorem failed_selection_exposes_a_generated_counterbranch (rounds : Nat) (state : State model)
    (absent : select model start vocabulary encoding law allowance rounds state = none)
    (plan : Plan model start vocabulary encoding law state)
    (generated : plan ∈ prepare model start vocabulary encoding law state) :
    ∃ move ∈ InterferenceEnvelope.choices start state.past allowance,
      guarantees model start vocabulary encoding law allowance rounds (after model start vocabulary encoding law state plan move) ≠ true := by
  have denied := List.find?_eq_none.mp absent plan generated
  simp only [List.all_eq_true, not_forall] at denied
  obtain ⟨move, inside, broken⟩ := denied
  exact ⟨move, inside, broken⟩

private theorem a_winning_node_has_a_selected_plan (rounds : Nat) (state : State model)
    (certified : (prepare model start vocabulary encoding law state).any (fun plan =>
      (InterferenceEnvelope.choices start state.past allowance).all fun move =>
        guarantees model start vocabulary encoding law allowance rounds (after model start vocabulary encoding law state plan move)) = true) :
    ∃ plan, select model start vocabulary encoding law allowance rounds state = some plan := by
  cases chosen : select model start vocabulary encoding law allowance rounds state with
  | some plan => exact ⟨plan, rfl⟩
  | none =>
    obtain ⟨plan, generated, worked⟩ := List.any_eq_true.mp certified
    exact False.elim ((List.find?_eq_none.mp chosen plan generated) worked)

inductive Status where
  | jointComplete | exhausted | observationCut | blocked | communicationViolation
  deriving DecidableEq
structure Result where
  state : State model
  status : Status
  inputs : List (InterferenceEnvelope.Input model.source.code)

def execute : Nat → State model → Opponent model.source.code → Result model
  | 0, state, _ => ⟨state, if Ready model start vocabulary encoding law state then .jointComplete
      else if CompletionState.fuel model start state = 0 then .exhausted else .observationCut, []⟩
  | rounds + 1, state, rival =>
    if Ready model start vocabulary encoding law state then ⟨state, .jointComplete, []⟩
    else if CompletionState.fuel model start state = 0 then ⟨state, .exhausted, []⟩
    else match continuation model start vocabulary encoding law allowance rounds state with
      | none => ⟨state, .blocked, []⟩
      | some plan =>
        let input := InterferenceEnvelope.observe start state.past allowance rival
        let actual := after model start vocabulary encoding law state plan input.admitted
        if input.within then
          let next := execute rounds actual rival
          ⟨next.state, next.status, input :: next.inputs⟩
        else ⟨actual, .communicationViolation, [input]⟩

def seeded (past : Stages model) := BatchRecoveryPlan.original model start vocabulary encoding law past
def guaranteed (past : Stages model) := guarantees model start vocabulary encoding law allowance
  (CompletionState.fuel model start (seeded model start vocabulary encoding law past))
  (seeded model start vocabulary encoding law past)
def produce (past : Stages model) (rival : Opponent model.source.code) := execute model start vocabulary encoding law allowance
  (CompletionState.fuel model start (seeded model start vocabulary encoding law past))
  (seeded model start vocabulary encoding law past) rival

theorem completion_is_the_entire_original_gate (state : State model) :
    Ready model start vocabulary encoding law state ↔ InterferenceValidity.Goal model start vocabulary encoding law state := by
  constructor
  · rintro ⟨closed, idle, native⟩
    refine ⟨⟨⟨native, idle⟩, ?_⟩, closed⟩
    intro entry member site needed
    obtain ⟨index, bounded, later, row, found, owned, submitted, _, stage, actual, protocol⟩ := closed entry member site needed
    exact ⟨index, bounded, later, row, found, owned, submitted, stage, actual, protocol⟩
  · intro complete
    exact ⟨complete.2, complete.1.1.2, complete.1.1.1⟩

theorem success_keeps_the_actual_complete_joint_gate (rounds : Nat) (state : State model) (rival : Opponent model.source.code)
    (accepted : (execute model start vocabulary encoding law allowance rounds state rival).status = .jointComplete) :
    Ready model start vocabulary encoding law (execute model start vocabulary encoding law allowance rounds state rival).state := by
  induction rounds generalizing state with
  | zero => dsimp only [execute] at accepted ⊢; split_ifs at accepted with complete; exact complete
  | succ rounds ih =>
    by_cases complete : Ready model start vocabulary encoding law state
    · simpa only [execute, if_pos complete] using complete
    · by_cases empty : CompletionState.fuel model start state = 0
      · simp only [execute, if_neg complete, if_pos empty] at accepted
        contradiction
      · simp only [execute, if_neg complete, if_neg empty] at accepted ⊢
        cases chosen : continuation model start vocabulary encoding law allowance rounds state with
        | none => simp only [chosen] at accepted; contradiction
        | some plan =>
          simp only [chosen] at accepted ⊢
          by_cases supported : (InterferenceEnvelope.observe start state.past allowance rival).within = true
          · simp only [if_pos supported] at accepted ⊢
            exact ih _ accepted
          · simp only [if_neg supported] at accepted
            contradiction

theorem every_compliant_adaptive_callback_completes (rounds : Nat) (state : State model)
    (rival : Opponent model.source.code)
    (certified : guarantees model start vocabulary encoding law allowance rounds state = true)
    (compliant : ((execute model start vocabulary encoding law allowance rounds state rival).inputs.all fun input => input.within) = true) :
    (execute model start vocabulary encoding law allowance rounds state rival).status = .jointComplete := by
  induction rounds generalizing state with
  | zero =>
    have complete := of_decide_eq_true certified
    simp only [execute, if_pos complete]
  | succ rounds ih =>
    by_cases complete : Ready model start vocabulary encoding law state
    · simp only [execute, if_pos complete]
    · by_cases empty : CompletionState.fuel model start state = 0
      · simp only [guarantees, if_neg complete, if_pos empty] at certified
        contradiction
      · simp only [guarantees, if_neg complete, if_neg empty] at certified
        obtain ⟨plan, chosen⟩ := a_winning_node_has_a_selected_plan model start vocabulary encoding law allowance rounds state certified
        have actualChosen := an_accepted_selection_is_the_actual_continuation model start vocabulary encoding law allowance rounds state plan chosen
        simp only [execute, if_neg complete, if_neg empty, actualChosen] at compliant ⊢
        by_cases supported : (InterferenceEnvelope.observe start state.past allowance rival).within = true
        · simp only [if_pos supported] at compliant ⊢
          have pair : (InterferenceEnvelope.observe start state.past allowance rival).within = true ∧
            ((execute model start vocabulary encoding law allowance rounds
              (after model start vocabulary encoding law state plan (InterferenceEnvelope.observe start state.past allowance rival).admitted) rival).inputs.all
              fun input => input.within) = true := by simpa only [List.all_cons, Bool.and_eq_true] using compliant
          exact ih _ (a_selected_plan_handles_every_generated_move model start vocabulary encoding law allowance rounds state plan chosen _
            (of_decide_eq_true supported)) pair.2
        · simp only [if_neg supported, List.all_cons, List.all_nil, Bool.and_true] at compliant
          contradiction

theorem execution_preserves_the_entire_registry_and_history (rounds : Nat) (state : State model)
    (rival : Opponent model.source.code) :
    state.past <+: (execute model start vocabulary encoding law allowance rounds state rival).state.past ∧
    state.batches ⊆ (execute model start vocabulary encoding law allowance rounds state rival).state.batches ∧
    (execute model start vocabulary encoding law allowance rounds state rival).state.past.length ≤ state.past.length + rounds := by
  induction rounds generalizing state with
  | zero => dsimp only [execute]; exact ⟨List.prefix_refl _, fun _ member => member, by omega⟩
  | succ rounds ih =>
    by_cases complete : Ready model start vocabulary encoding law state
    · simp only [execute, if_pos complete]
      exact ⟨List.prefix_refl _, fun _ member => member, by omega⟩
    · by_cases empty : CompletionState.fuel model start state = 0
      · simp only [execute, if_neg complete, if_pos empty]
        exact ⟨List.prefix_refl _, fun _ member => member, by omega⟩
      · simp only [execute, if_neg complete, if_neg empty]
        cases chosen : continuation model start vocabulary encoding law allowance rounds state with
        | none =>
          exact ⟨List.prefix_refl _, fun _ member => member, by
            change state.past.length ≤ state.past.length + (rounds + 1)
            omega⟩
        | some plan =>
          have old := every_edge_retains_all_old_entries model start vocabulary encoding law state plan
            (InterferenceEnvelope.observe start state.past allowance rival).admitted
          by_cases supported : (InterferenceEnvelope.observe start state.past allowance rival).within = true
          · simp only [if_pos supported]
            have rest := ih (after model start vocabulary encoding law state plan (InterferenceEnvelope.observe start state.past allowance rival).admitted)
            refine ⟨(List.prefix_append _ _).trans rest.1, fun entry member => rest.2.1 (old member), ?_⟩
            have bound := rest.2.2
            have edgeLength : (after model start vocabulary encoding law state plan
                (InterferenceEnvelope.observe start state.past allowance rival).admitted).past.length = state.past.length + 1 := by
              simp only [after, List.length_append, List.length_singleton]
            rw [edgeLength] at bound
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
          · simp only [if_neg supported]
            exact ⟨List.prefix_append _ _, old, by simp [after]⟩

theorem execution_preserves_actual_batch_sources (rounds : Nat) (state : State model)
    (rival : Opponent model.source.code) (retained : CompletionState.entriesAreActualPrefixes model state) :
    CompletionState.entriesAreActualPrefixes model (execute model start vocabulary encoding law allowance rounds state rival).state := by
  induction rounds generalizing state with
  | zero => dsimp only [execute]; exact retained
  | succ rounds ih =>
    by_cases complete : Ready model start vocabulary encoding law state
    · simpa only [execute, if_pos complete] using retained
    · by_cases empty : CompletionState.fuel model start state = 0
      · simpa only [execute, if_neg complete, if_pos empty] using retained
      · simp only [execute, if_neg complete, if_neg empty]
        cases chosen : continuation model start vocabulary encoding law allowance rounds state with
        | none => exact retained
        | some plan =>
          have next := every_edge_retains_actual_batch_sources model start vocabulary encoding law state plan
            (InterferenceEnvelope.observe start state.past allowance rival).admitted retained
          by_cases supported : (InterferenceEnvelope.observe start state.past allowance rival).within = true
          · simpa only [if_pos supported] using ih _ next
          · simpa only [if_neg supported] using next

theorem compliant_execution_cannot_refill_the_source_deviation_budget
    (rounds : Nat) (state : State model) (rival : Opponent model.source.code)
    (compliant : ((execute model start vocabulary encoding law allowance rounds state rival).inputs.all
      fun input => input.within) = true) :
    InterferenceEnvelope.spent start (execute model start vocabulary encoding law allowance rounds state rival).state.past ≤
      max model.source.code.eventLimit (InterferenceEnvelope.spent start state.past) := by
  induction rounds generalizing state with
  | zero => exact Nat.le_max_right _ _
  | succ rounds ih =>
    by_cases complete : Ready model start vocabulary encoding law state
    · simpa only [execute, if_pos complete] using Nat.le_max_right model.source.code.eventLimit (InterferenceEnvelope.spent start state.past)
    · by_cases empty : CompletionState.fuel model start state = 0
      · simpa only [execute, if_neg complete, if_pos empty] using Nat.le_max_right model.source.code.eventLimit (InterferenceEnvelope.spent start state.past)
      · simp only [execute, if_neg complete, if_neg empty] at compliant ⊢
        cases chosen : continuation model start vocabulary encoding law allowance rounds state with
        | none => exact Nat.le_max_right _ _
        | some plan =>
          simp only [chosen] at compliant
          by_cases supported : (InterferenceEnvelope.observe start state.past allowance rival).within = true
          · simp only [if_pos supported] at compliant ⊢
            have pair : (InterferenceEnvelope.observe start state.past allowance rival).within = true ∧
                ((execute model start vocabulary encoding law allowance rounds
                  (after model start vocabulary encoding law state plan (InterferenceEnvelope.observe start state.past allowance rival).admitted) rival).inputs.all
                    fun input => input.within) = true := by simpa only [List.all_cons, Bool.and_eq_true] using compliant
            have edge := InterferenceEnvelope.a_supported_actual_step_preserves_the_source_interface_bound
              start state.past allowance (rule model start vocabulary encoding law plan)
              (InterferenceEnvelope.observe start state.past allowance rival).admitted
              (InterferenceEnvelope.external_intake_is_idempotent _) (of_decide_eq_true supported)
            have rest := ih _ pair.2
            exact rest.trans (Nat.max_le.mpr ⟨Nat.le_max_left _ _, edge⟩)
          · simp only [if_neg supported, List.all_cons, List.all_nil, Bool.and_true] at compliant
            contradiction

theorem success_consumes_every_original_source_registered_intent (past : Stages model) (rival : Opponent model.source.code)
    (accepted : (produce model start vocabulary encoding law allowance past rival).status = .jointComplete) :
    ∀ entry ∈ (BatchReentry.produce model start vocabulary encoding law past).batches, ∀ site,
      RetainedIntent.intent vocabulary encoding law start entry site ≠ [] →
        InterferenceValidity.served model start vocabulary encoding law entry
          (produce model start vocabulary encoding law allowance past rival).state.past site := by
  have ready := success_keeps_the_actual_complete_joint_gate model start vocabulary encoding law allowance _ _ rival accepted
  have kept := (execution_preserves_the_entire_registry_and_history model start vocabulary encoding law allowance
    (CompletionState.fuel model start (seeded model start vocabulary encoding law past))
    (seeded model start vocabulary encoding law past) rival).2.1
  exact fun entry member site nonempty => ready.1 entry (kept member) site nonempty

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StrategyRun
