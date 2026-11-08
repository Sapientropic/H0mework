import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionTree

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionExecution

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open CompletionState CompletionTree

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

inductive Status where
  | jointComplete | halted (reason : Halt) | communicationViolation
  deriving DecidableEq

structure Result where
  state : State model
  status : Status
  inputs : List (CompletionEnvelope.Input model.source.code)

-- The callback is read at the actual cut. Even an input outside the envelope
-- takes its real admitted step before returning a violation and the raw intake.
def follow {state : State model} (tree : Tree model start vocabulary encoding law allowance state)
    (rival : Opponent model.source.code) : Result model :=
  match tree with
  | .done _ => ⟨state, .jointComplete, []⟩
  | .halted reason => ⟨state, .halted reason, []⟩
  | .node plan children =>
    let input := CompletionEnvelope.observe start state.past allowance rival
    if supported : input.admitted ∈ CompletionEnvelope.choices start state.past allowance then
      let next := follow (children ⟨input.admitted, supported⟩) rival
      ⟨next.state, next.status, input :: next.inputs⟩
    else ⟨after model start vocabulary encoding law state plan input.admitted, .communicationViolation, [input]⟩

-- Independent actual execution does not consume a proposed terminal leaf.
def execute : Nat → State model → Opponent model.source.code → Result model
  | 0, state, _ => if Goal model start vocabulary encoding law state then ⟨state, .jointComplete, []⟩
      else if fuel model start state = 0 then ⟨state, .halted .exhausted, []⟩ else ⟨state, .halted .observationCut, []⟩
  | rounds + 1, state, rival =>
    if Goal model start vocabulary encoding law state then ⟨state, .jointComplete, []⟩
    else if fuel model start state = 0 then ⟨state, .halted .exhausted, []⟩
    else match prepare model start vocabulary encoding law state with
      | .halted reason => ⟨state, .halted reason, []⟩
      | .ready plan =>
        let input := CompletionEnvelope.observe start state.past allowance rival
        let actual := after model start vocabulary encoding law state plan input.admitted
        if input.admitted ∈ CompletionEnvelope.choices start state.past allowance then
          let next := execute rounds actual rival
          ⟨next.state, next.status, input :: next.inputs⟩
        else ⟨actual, .communicationViolation, [input]⟩

theorem independent_execution_equals_the_actual_generated_branch
    (rounds : Nat) (state : State model) (rival : Opponent model.source.code) :
    execute model start vocabulary encoding law allowance rounds state rival =
      follow model start vocabulary encoding law allowance (build model start vocabulary encoding law allowance rounds state) rival := by
  induction rounds generalizing state with
  | zero => simp only [execute, build]; split_ifs <;> rfl
  | succ rounds ih =>
    by_cases complete : Goal model start vocabulary encoding law state
    · simp only [execute, build, dif_pos complete, if_pos complete, follow]
    · by_cases empty : fuel model start state = 0
      · simp only [execute, build, dif_neg complete, if_neg complete, if_pos empty, follow]
      · cases selected : prepare model start vocabulary encoding law state with
        | halted reason => simp only [execute, build, dif_neg complete, if_neg complete, if_neg empty, selected, follow]
        | ready plan =>
          simp only [execute, build, dif_neg complete, if_neg complete, if_neg empty, selected, follow]
          split_ifs
          · rw [ih]
          · rfl

def produce (past : BatchReentry.Stages model) (rival : Opponent model.source.code) :=
  execute model start vocabulary encoding law allowance (BatchReentry.fuel model start past) (initial model past) rival

theorem every_execution_keeps_the_whole_actual_prefix {state : State model}
    (tree : Tree model start vocabulary encoding law allowance state) (rival : Opponent model.source.code) :
    state.past <+: (follow model start vocabulary encoding law allowance tree rival).state.past := by
  induction tree with
  | done => exact List.prefix_refl _
  | halted => exact List.prefix_refl _
  | @node state plan children ih =>
    dsimp only [follow]
    split
    · exact (an_actual_edge_preserves_every_prior_stage model start vocabulary encoding law state plan _).trans (ih _)
    · exact an_actual_edge_preserves_every_prior_stage model start vocabulary encoding law state plan _

theorem every_execution_keeps_batch_entries_as_actual_prefixes {state : State model}
    (tree : Tree model start vocabulary encoding law allowance state) (rival : Opponent model.source.code)
    (retained : entriesAreActualPrefixes model state) :
    entriesAreActualPrefixes model (follow model start vocabulary encoding law allowance tree rival).state := by
  induction tree with
  | done => exact retained
  | halted => exact retained
  | @node state plan children ih =>
    dsimp only [follow]
    split
    · exact ih _ (an_actual_edge_preserves_all_batch_entry_prefixes model start vocabulary encoding law state plan _ retained)
    · exact an_actual_edge_preserves_all_batch_entry_prefixes model start vocabulary encoding law state plan _ retained

theorem completion_keeps_every_latest_gate_and_every_original_batch {state : State model}
    (tree : Tree model start vocabulary encoding law allowance state) (rival : Opponent model.source.code)
    (complete : (follow model start vocabulary encoding law allowance tree rival).status = .jointComplete) :
    Goal model start vocabulary encoding law (follow model start vocabulary encoding law allowance tree rival).state := by
  induction tree with
  | done finished => exact finished
  | halted => contradiction
  | @node state plan children ih =>
    dsimp only [follow] at complete ⊢
    split_ifs at complete ⊢
    exact ih _ complete

theorem generated_winning_tree_guarantees_completion_for_every_compliant_adaptive_input
    {state : State model} (tree : Tree model start vocabulary encoding law allowance state)
    (rival : Opponent model.source.code)
    (accepted : winning model start vocabulary encoding law allowance tree = true)
    (compliant : ((follow model start vocabulary encoding law allowance tree rival).inputs.all fun input => input.within) = true) :
    (follow model start vocabulary encoding law allowance tree rival).status = .jointComplete := by
  induction tree with
  | done => rfl
  | halted => contradiction
  | @node state plan children ih =>
    dsimp only [follow] at compliant ⊢
    split_ifs at compliant ⊢
    · rename_i supported
      have pair : (CompletionEnvelope.observe start state.past allowance rival).within = true ∧
          ((follow model start vocabulary encoding law allowance (children ⟨_, supported⟩) rival).inputs.all fun input => input.within) = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using compliant
      have rest := pair.2
      exact ih _ (every_branch_of_a_generated_winning_node_is_winning model start vocabulary encoding law allowance plan children accepted _) rest
    · rename_i outside
      have denied : (CompletionEnvelope.observe start state.past allowance rival).within = false :=
        decide_eq_false outside
      simp only [List.all_cons, List.all_nil, denied, Bool.false_and, Bool.false_eq_true] at compliant

private theorem initial_le_maximum (items : List Nat) (initial : Nat) : initial ≤ items.foldl max initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons head tail ih => exact (Nat.le_max_left _ _).trans (ih _)

private theorem member_le_maximum (items : List Nat) (initial item : Nat) (member : item ∈ items) :
    item ≤ items.foldl max initial := by
  induction items generalizing initial with
  | nil => contradiction
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst item
      exact (Nat.le_max_right _ _).trans (initial_le_maximum tail _)
    · exact ih _ later

theorem the_generated_tree_height_bounds_the_actual_execution {state : State model}
    (tree : Tree model start vocabulary encoding law allowance state) (rival : Opponent model.source.code) :
    (follow model start vocabulary encoding law allowance tree rival).state.past.length ≤
      state.past.length + height model start vocabulary encoding law allowance tree := by
  induction tree with
  | done => simp [follow, height]
  | halted => simp [follow, height]
  | @node state plan children ih =>
    dsimp only [follow]
    split
    · rename_i supported
      let move : Choices model start allowance state := ⟨(CompletionEnvelope.observe start state.past allowance rival).admitted, supported⟩
      have rest := ih move
      have bound := member_le_maximum
        ((CompletionEnvelope.choices start state.past allowance).attach.map fun item => height model start vocabulary encoding law allowance (children item))
        0 (height model start vocabulary encoding law allowance (children move))
        (List.mem_map.mpr ⟨move, List.mem_attach _ _, rfl⟩)
      simp only [after, List.length_append, List.length_singleton] at rest
      change (follow model start vocabulary encoding law allowance (children move) rival).state.past.length ≤
        state.past.length + (1 + ((CompletionEnvelope.choices start state.past allowance).attach.map fun item =>
          height model start vocabulary encoding law allowance (children item)).foldl max 0)
      calc
        _ ≤ state.past.length + 1 + height model start vocabulary encoding law allowance (children move) := rest
        _ ≤ _ := by omega
    · simp only [after, List.length_append, List.length_singleton, height]
      omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionExecution
