import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.TimedRetryRuntime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResponseSweep

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedResponse

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
abbrev current (past : Stages model) := EventHistory.execute start past
def fuel (past : Stages model) := (EventStep.seed (current model start past)).remaining
abbrev incidents (past : Stages model) := ResponseSweep.unhandled model start vocabulary encoding law past

def rejections (past : Stages model) : List (RejectionResponse.Identity model) :=
  ((List.finRange model.source.code.sites).flatMap fun receiver =>
    (ReceptionEvidence.observed start past vocabulary encoding law receiver).map fun entry => (receiver, entry.index)).filter
      (fun identity => decide (identity ∉ (RejectionResponse.journal model start past vocabulary encoding law).map
        (RejectionResponse.Answer.id model start vocabulary encoding law)))

def duties (past : Stages model) :=
  (StageDuty.origins start vocabulary encoding past).filter fun emission =>
    decide (¬ TimedDuty.Confirmed start past vocabulary encoding law emission)

-- Pending, unexpired content also prevents completion; absence of Overdue is insufficient.
def Clear (past : Stages model) : Prop :=
  incidents model start vocabulary encoding law past = [] ∧
    rejections model start vocabulary encoding law past = [] ∧ duties model start vocabulary encoding law past = []

instance (past : Stages model) : Decidable (Clear model start vocabulary encoding law past) := by
  unfold Clear; infer_instance

inductive Action (past : Stages model) where
  | conflict (response : IncidentResponse.Ready model start past vocabulary encoding law)
      (actual : IncidentResponse.produce model start past vocabulary encoding law = .ready response)
  | rejection (response : RejectionResponse.Ready model start past vocabulary encoding law)
      (actual : RejectionResponse.produce model start past vocabulary encoding law = .ready response)
  | retry (answer : TimedRetry.Ready start past vocabulary encoding law)
      (actual : TimedRetry.produce start past vocabulary encoding law = .ready answer)
  | wait (live : 0 < fuel model start past)

inductive Kind where
  | conflict | rejection | retry | wait
  deriving DecidableEq

def kind {past : Stages model} : Action model start vocabulary encoding law past → Kind
  | .conflict _ _ => .conflict
  | .rejection _ _ => .rejection
  | .retry _ _ => .retry
  | .wait _ => .wait

def after (past : Stages model) : Action model start vocabulary encoding law past → Stages model
  | .conflict response _ => past ++ [(IncidentResponse.protocol model start past vocabulary encoding law response, OriginQueue.environment start)]
  | .rejection response _ => past ++ [(RejectionResponse.protocol model start past vocabulary encoding law response, OriginQueue.environment start)]
  | .retry answer _ => answer.stages
  | .wait _ => past ++ [(SilentWindow.quiet, OriginQueue.environment start)]

inductive Step (past : Stages model) where
  | clear (covered : Clear model start vocabulary encoding law past)
  | exhausted (empty : fuel model start past = 0)
  | advance (action : Action model start vocabulary encoding law past)

-- Available native responses precede repair; each iteration reobserves the actual successor.
def step (past : Stages model) : Step model start vocabulary encoding law past :=
  if covered : Clear model start vocabulary encoding law past then .clear covered
  else if live : 0 < fuel model start past then
    match conflict : IncidentResponse.produce model start past vocabulary encoding law with
    | .ready response => .advance (.conflict response conflict)
    | _ => match rejected : RejectionResponse.produce model start past vocabulary encoding law with
      | .ready response => .advance (.rejection response rejected)
      | _ => match retried : TimedRetry.produce start past vocabulary encoding law with
        | .ready answer => .advance (.retry answer retried)
        | _ => .advance (.wait live)
  else .exhausted (by omega)

theorem every_action_retains_the_actual_prefix (past : Stages model)
    (action : Action model start vocabulary encoding law past) :
    past <+: after model start vocabulary encoding law past action := by
  cases action with
  | conflict response actual => exact List.prefix_append _ _
  | rejection response actual => exact List.prefix_append _ _
  | retry answer actual => exact TimedRetry.the_original_history_is_preserved start past vocabulary encoding law answer
  | wait live => exact List.prefix_append _ _

theorem fuel_after_actual_extension (past more : Stages model) :
    fuel model start (past ++ more) = fuel model start past - more.length := by
  unfold fuel current
  rw [OriginQueue.execute_append]
  generalize EventHistory.execute start past = cursor
  induction more generalizing cursor with
  | nil => rfl
  | cons stage tail ih =>
    change (EventStep.seed (EventHistory.execute (cursor.after stage.1 stage.2) tail)).remaining = _
    rw [ih, EventStep.actual_next_state]
    change (EventStep.seed cursor).remaining - 1 - tail.length = (EventStep.seed cursor).remaining - (tail.length + 1)
    omega

theorem every_action_spends_actual_fuel (past : Stages model)
    (action : Action model start vocabulary encoding law past) :
    fuel model start (after model start vocabulary encoding law past action) < fuel model start past := by
  cases action with
  | conflict response actual =>
    change fuel model start (past ++ [_]) < _
    rw [fuel_after_actual_extension]
    have positive := response.fuel
    change 0 < fuel model start past at positive
    simp only [List.length_singleton]
    omega
  | rejection response actual =>
    change fuel model start (past ++ [_]) < _
    rw [fuel_after_actual_extension]
    have positive := response.fuel
    change 0 < fuel model start past at positive
    simp only [List.length_singleton]
    omega
  | retry answer actual =>
    have paid := answer.fuel
    change TimedRetry.waiting start past vocabulary encoding law answer.overdue + 2 ≤ fuel model start past at paid
    change fuel model start answer.stages < _
    simp only [TimedRetry.Ready.stages, TimedRetry.completed, TimedRetry.sent, TimedRetry.aligned,
      fuel_after_actual_extension, List.length_singleton, SilentWindow.stage_count]
    omega
  | wait live =>
    change fuel model start (past ++ [_]) < _
    rw [fuel_after_actual_extension]
    simp only [List.length_singleton]
    omega

theorem clear_covers_every_original_duty (past : Stages model)
    (covered : Clear model start vocabulary encoding law past) :
    ∀ row ∈ StageDuty.histories start vocabulary encoding law past, row.2.2.state.TerminalAt 0 := by
  intro row inside
  obtain ⟨emission, original, same⟩ := List.mem_map.mp inside
  cases same
  apply (StageDuty.generated_row_terminal_iff_the_actual_receiver_confirms start vocabulary encoding law past _ inside).mpr
  by_contra missing
  have pending : emission ∈ duties model start vocabulary encoding law past :=
    List.mem_filter.mpr ⟨original, decide_eq_true missing⟩
  rw [covered.2.2] at pending
  exact List.not_mem_nil pending

theorem clear_covers_every_actual_incident (past : Stages model)
    (covered : Clear model start vocabulary encoding law past) :
    ∀ incident ∈ StageAccountability.ledger start vocabulary encoding law past,
      IncidentResponse.identity model start vocabulary encoding law incident ∈
        (IncidentResponse.journal model start past vocabulary encoding law).map (IncidentResponse.Answer.id model start vocabulary encoding law) := by
  intro incident inside
  by_contra missing
  have pending : incident ∈ incidents model start vocabulary encoding law past :=
    List.mem_filter.mpr ⟨inside, decide_eq_true missing⟩
  rw [covered.1] at pending
  exact List.not_mem_nil pending

theorem clear_covers_every_actual_rejection (past : Stages model)
    (covered : Clear model start vocabulary encoding law past) (receiver : Fin model.source.code.sites) :
    ∀ evidence ∈ ReceptionEvidence.observed start past vocabulary encoding law receiver,
      (receiver, evidence.index) ∈ (RejectionResponse.journal model start past vocabulary encoding law).map
        (RejectionResponse.Answer.id model start vocabulary encoding law) := by
  intro evidence inside
  by_contra missing
  have pending : (receiver, evidence.index) ∈ rejections model start vocabulary encoding law past :=
    List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨receiver, by simp,
      List.mem_map.mpr ⟨evidence, inside, rfl⟩⟩, decide_eq_true missing⟩
  rw [covered.2.1] at pending
  exact List.not_mem_nil pending

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedResponse
