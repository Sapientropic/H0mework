import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionEnvelope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionState

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

abbrev Stages := BatchReentry.Stages model

structure State where
  past : Stages model
  todo : List (Rule model.source.code)
  batches : List (Stages model)

abbrev current (state : State model) := EventHistory.execute start state.past
abbrev fuel (state : State model) := (EventStep.seed (current model start state)).remaining

def served (entry past : Stages model) (site : Fin model.source.code.sites) : Prop :=
  ∃ index ∈ List.range past.length,
    entry.length ≤ index ∧ ∃ row, (StageTrace.records start past)[index]? = some row ∧
      StageTrace.activation row = some site ∧
      row.submitted = RetainedIntent.intent vocabulary encoding law start entry site ∧
      ∃ stage, past[index]? = some stage ∧
        IncidentResponse.sameRule model stage.1 (RetainedIntent.protocol vocabulary encoding law start entry) = true
instance (entry past : Stages model) (site : Fin model.source.code.sites) :
    Decidable (served model start vocabulary encoding law entry past site) := by
  unfold served
  infer_instance

def batchesClosed (state : State model) : Prop :=
  ∀ entry ∈ state.batches, ∀ site,
    RetainedIntent.intent vocabulary encoding law start entry site ≠ [] →
      served model start vocabulary encoding law entry state.past site
instance (state : State model) : Decidable (batchesClosed model start vocabulary encoding law state) := by
  unfold batchesClosed; infer_instance

def Goal (state : State model) : Prop :=
  BatchReentry.Clear model start vocabulary encoding law state.past ∧ batchesClosed model start vocabulary encoding law state
instance (state : State model) : Decidable (Goal model start vocabulary encoding law state) := by
  unfold Goal; infer_instance

-- The plan is an actual prefix-preserving native action, or the remainder of
-- an already installed word. Neither constructor accepts a new caller menu.
inductive Plan (state : State model) where
  | queued (head : Rule model.source.code) (tail : List (Rule model.source.code)) (actual : state.todo = head :: tail)
  | fresh (action : BatchReentry.Action model start vocabulary encoding law state.past)
      (actual : BatchReentry.step model start vocabulary encoding law state.past = .advance action)

def program {state : State model} : Plan model start vocabulary encoding law state → List (Rule model.source.code)
  | .queued head tail _ => head :: tail
  | .fresh action _ => (BatchReentry.after model start vocabulary encoding law state.past action).drop state.past.length |>.map Prod.fst

def jobs {state : State model} : Plan model start vocabulary encoding law state → List (Stages model)
  | .queued _ _ _ => state.batches
  | .fresh (.batch _ _) _ => state.past :: state.batches
  | .fresh (.native _) _ => state.batches

theorem program_nonempty {state : State model} (plan : Plan model start vocabulary encoding law state) :
    program model start vocabulary encoding law plan ≠ [] := by
  cases plan with
  | queued => simp [program]
  | fresh action actual =>
    intro empty
    obtain ⟨more, extended⟩ := BatchReentry.every_action_keeps_the_actual_prefix model start vocabulary encoding law state.past action
    have noMore : more = [] := by
      simpa [program, ← extended, List.drop_left] using empty
    have spent := BatchReentry.every_action_spends_actual_fuel model start vocabulary encoding law state.past action
    rw [← extended, noMore, List.append_nil] at spent
    exact (Nat.lt_irrefl _) spent

def rule {state : State model} (plan : Plan model start vocabulary encoding law state) : Rule model.source.code :=
  (program model start vocabulary encoding law plan).headD SilentWindow.quiet

def after (state : State model) (plan : Plan model start vocabulary encoding law state) (move : Move model.source.code) : State model :=
  ⟨state.past ++ [(rule model start vocabulary encoding law plan, EventStep.fixed move)],
    (program model start vocabulary encoding law plan).drop 1, jobs model start vocabulary encoding law plan⟩

theorem an_actual_edge_preserves_every_prior_stage (state : State model)
    (plan : Plan model start vocabulary encoding law state) (move : Move model.source.code) :
    state.past <+: (after model start vocabulary encoding law state plan move).past := List.prefix_append _ _

theorem every_actual_edge_spends_one_source_tick (state : State model)
    (plan : Plan model start vocabulary encoding law state) (move : Move model.source.code) :
    fuel model start (after model start vocabulary encoding law state plan move) = fuel model start state - 1 := by
  change BatchReentry.fuel model start (state.past ++ [_]) = BatchReentry.fuel model start state.past - 1
  simp only [BatchReentry.fuel, LocalJointResponse.fuel, UnifiedResponse.fuel_after_actual_extension, List.length_singleton]

inductive Halt where
  | exhausted | sourceRefused (reason : IntentServiceRun.Status) | unservedBatch | observationCut
  deriving DecidableEq

inductive Preparation (state : State model) where
  | ready (plan : Plan model start vocabulary encoding law state)
  | halted (reason : Halt)

def prepare (state : State model) : Preparation model start vocabulary encoding law state :=
  match pending : state.todo with
  | head :: tail => .ready (.queued head tail pending)
  | [] => match selected : BatchReentry.step model start vocabulary encoding law state.past with
    | .complete _ => .halted .unservedBatch
    | .exhausted _ _ => .halted .exhausted
    | .refused _ _ => .halted (.sourceRefused (BatchReentry.service model start vocabulary encoding law state.past).status)
    | .advance action => .ready (.fresh action selected)

def entriesAreActualPrefixes (state : State model) : Prop := ∀ entry ∈ state.batches, entry <+: state.past

theorem an_actual_edge_preserves_all_batch_entry_prefixes (state : State model)
    (plan : Plan model start vocabulary encoding law state) (move : Move model.source.code)
    (retained : entriesAreActualPrefixes model state) :
    entriesAreActualPrefixes model (after model start vocabulary encoding law state plan move) := by
  intro entry member
  have extension := an_actual_edge_preserves_every_prior_stage model start vocabulary encoding law state plan move
  cases plan with
  | queued => exact (retained entry member).trans extension
  | fresh action selected =>
    cases action with
    | batch =>
      rcases List.mem_cons.mp member with same | old
      · subst entry; exact extension
      · exact (retained entry old).trans extension
    | native => exact (retained entry member).trans extension

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionState
