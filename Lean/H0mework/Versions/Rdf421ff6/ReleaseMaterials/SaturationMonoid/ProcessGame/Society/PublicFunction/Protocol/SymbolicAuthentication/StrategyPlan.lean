import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointRecoveryPlan
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SupplyMenu

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StrategyPlan

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

abbrev State := CompletionState.State model
abbrev Stages := BatchReentry.Stages model

def attempted (state : State model) :=
  ((BatchReentry.service model start vocabulary encoding law state.past).stages.drop state.past.length).map Prod.fst

def recoveryProgram (state : State model) (entry : Stages model) (rank : Nat) :=
  List.replicate (RecoveryWindow.supplyCount model start state.past)
    (SupplyMenu.protocol vocabulary law start state.past rank) ++
  List.replicate (RecoveryWindow.serviceCount model start state.past)
    (RetainedIntent.protocol vocabulary encoding law start entry)

def captureProgram (state : State model) (rank : Nat) :=
  let pendingRules := attempted model start vocabulary encoding law state
  if pendingRules = [] then recoveryProgram model start vocabulary encoding law state state.past rank else pendingRules

def ranks := List.range (model.source.code.actions.length + 1)

theorem every_recovery_candidate_keeps_the_literal_original_service_suffix
    (state : State model) (entry : Stages model) (rank : Nat) :
    (recoveryProgram model start vocabulary encoding law state entry rank).drop
        (RecoveryWindow.supplyCount model start state.past) =
      List.replicate (RecoveryWindow.serviceCount model start state.past)
        (RetainedIntent.protocol vocabulary encoding law start entry) := by
  simp [recoveryProgram]

inductive Plan (state : State model) where
  | queued (head : Rule model.source.code) (tail : List (Rule model.source.code))
      (actual : state.todo = head :: tail)
  | restore (task : BatchRecoveryPlan.Task model) (rank : Nat)
      (selected : BatchRecoveryPlan.select model start vocabulary encoding law state = some task)
      (nonempty : recoveryProgram model start vocabulary encoding law state task.1 rank ≠ [])
  | native (plan : CompletionState.Plan model start vocabulary encoding law state)
  | capture (rank : Nat) (reason : IntentServiceRun.Status)
      (refused : CompletionState.prepare model start vocabulary encoding law state = .halted (.sourceRefused reason))
      (nonempty : captureProgram model start vocabulary encoding law state rank ≠ [])

def program {state : State model} : Plan model start vocabulary encoding law state → List (Rule model.source.code)
  | .queued head tail _ => head :: tail
  | .restore task rank _ _ => recoveryProgram model start vocabulary encoding law state task.1 rank
  | .native plan => CompletionState.program model start vocabulary encoding law plan
  | .capture rank _ _ _ => captureProgram model start vocabulary encoding law state rank

def jobs {state : State model} : Plan model start vocabulary encoding law state → List (Stages model)
  | .queued _ _ _ | .restore _ _ _ _ => state.batches
  | .native plan => CompletionState.jobs model start vocabulary encoding law plan
  | .capture _ _ _ _ => state.past :: state.batches

theorem program_nonempty {state : State model} (plan : Plan model start vocabulary encoding law state) :
    program model start vocabulary encoding law plan ≠ [] := by
  cases plan with
  | queued => simp [program]
  | restore task rank selected nonempty => exact nonempty
  | native plan => exact CompletionState.program_nonempty model start vocabulary encoding law plan
  | capture rank reason refused nonempty => exact nonempty

def rule {state : State model} (plan : Plan model start vocabulary encoding law state) :=
  (program model start vocabulary encoding law plan).headD SilentWindow.quiet

def after (state : State model) (plan : Plan model start vocabulary encoding law state)
    (move : Move model.source.code) : State model :=
  ⟨state.past ++ [(rule model start vocabulary encoding law plan, EventStep.fixed move)],
    (program model start vocabulary encoding law plan).drop 1, jobs model start vocabulary encoding law plan⟩

-- Only an unstarted recovery segment admits a source-generated choice. The
-- installed tail and any partial native attempt retain their literal rules.
def prepare (state : State model) : List (Plan model start vocabulary encoding law state) :=
  match pending : state.todo with
  | head :: tail => [.queued head tail pending]
  | [] => match selected : BatchRecoveryPlan.select model start vocabulary encoding law state with
    | some task => (ranks model).filterMap fun rank =>
      if nonempty : recoveryProgram model start vocabulary encoding law state task.1 rank ≠ [] then
        some (.restore task rank selected nonempty) else none
    | none => match actual : CompletionState.prepare model start vocabulary encoding law state with
      | .ready plan => [.native plan]
      | .halted (.sourceRefused reason) => (ranks model).filterMap fun rank =>
        if nonempty : captureProgram model start vocabulary encoding law state rank ≠ [] then
          some (.capture rank reason actual nonempty) else none
      | .halted _ => []

theorem every_edge_retains_all_old_entries (state : State model)
    (plan : Plan model start vocabulary encoding law state) (move : Move model.source.code) :
    state.batches ⊆ (after model start vocabulary encoding law state plan move).batches := by
  cases plan with
  | queued => exact fun _ member => member
  | restore => exact fun _ member => member
  | capture => exact fun _ member => List.mem_cons_of_mem _ member
  | native plan =>
    cases plan with
    | queued => exact fun _ member => member
    | fresh action selected =>
      cases action with
      | batch => exact fun _ member => List.mem_cons_of_mem _ member
      | native => exact fun _ member => member

theorem every_edge_retains_actual_batch_sources (state : State model)
    (plan : Plan model start vocabulary encoding law state) (move : Move model.source.code)
    (retained : CompletionState.entriesAreActualPrefixes model state) :
    CompletionState.entriesAreActualPrefixes model (after model start vocabulary encoding law state plan move) := by
  have extension : state.past <+: (after model start vocabulary encoding law state plan move).past := List.prefix_append _ _
  cases plan with
  | queued => exact fun entry member => (retained entry member).trans extension
  | restore => exact fun entry member => (retained entry member).trans extension
  | native plan =>
    exact CompletionState.an_actual_edge_preserves_all_batch_entry_prefixes model start vocabulary encoding law state plan move retained
  | capture =>
    intro entry member
    rcases List.mem_cons.mp member with same | old
    · subst entry; exact extension
    · exact (retained entry old).trans extension

theorem capture_keeps_the_entire_original_partial_program (state : State model) (rank : Nat)
    (nonempty : attempted model start vocabulary encoding law state ≠ []) :
    captureProgram model start vocabulary encoding law state rank = attempted model start vocabulary encoding law state := by
  simp only [captureProgram, if_neg nonempty]

theorem refusal_is_an_actual_new_nonempty_intent (state : State model) (reason : IntentServiceRun.Status)
    (refused : CompletionState.prepare model start vocabulary encoding law state = .halted (.sourceRefused reason)) :
    ∃ site, RetainedIntent.intent vocabulary encoding law start state.past site ≠ [] := by
  unfold CompletionState.prepare at refused
  split at refused
  · contradiction
  · split at refused
    · cases refused
    · cases refused
    · have needed : ¬ BatchReentry.idle model start vocabulary encoding law state.past := by assumption
      simpa only [BatchReentry.idle, not_forall] using needed
    · contradiction

theorem capture_registers_the_actual_birth_before_its_next_physical_step (state : State model) (rank : Nat)
    (reason : IntentServiceRun.Status)
    (refused : CompletionState.prepare model start vocabulary encoding law state = .halted (.sourceRefused reason))
    (nonempty : captureProgram model start vocabulary encoding law state rank ≠ []) (move : Move model.source.code) :
    (after model start vocabulary encoding law state (.capture rank reason refused nonempty) move).batches = state.past :: state.batches ∧
    ∃ site, RetainedIntent.intent vocabulary encoding law start state.past site ≠ [] :=
  ⟨rfl, refusal_is_an_actual_new_nonempty_intent model start vocabulary encoding law state reason refused⟩

theorem every_edge_spends_exactly_one_source_tick (state : State model)
    (plan : Plan model start vocabulary encoding law state) (move : Move model.source.code) :
    CompletionState.fuel model start (after model start vocabulary encoding law state plan move) =
      CompletionState.fuel model start state - 1 := by
  change UnifiedResponse.fuel model start (state.past ++ [_]) = UnifiedResponse.fuel model start state.past - 1
  simp only [UnifiedResponse.fuel_after_actual_extension, List.length_singleton]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StrategyPlan
