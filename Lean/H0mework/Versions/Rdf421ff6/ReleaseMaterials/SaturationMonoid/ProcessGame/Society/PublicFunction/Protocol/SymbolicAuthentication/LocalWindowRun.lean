import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalWindowPlan
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BatchRecoveryPlan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalWindowRun

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
  (allowance : Nat)

abbrev Stages := BatchReentry.Stages model
abbrev State := CompletionState.State model

-- Every actual historical snapshot is retained, including the final one. This
-- audit is not an input to the public programme or its physical execution.
def snapshots (past : Stages model) := (List.range (past.length + 1)).map past.take
def audit (past : Stages model) (pending : List (Rule model.source.code)) : State model :=
  ⟨past, pending, snapshots model past⟩

def Ready (state : State model) : Prop := state.todo = [] ∧ InterferenceValidity.Goal model start vocabulary encoding law state
instance (state : State model) : Decidable (Ready model start vocabulary encoding law state) := by
  unfold Ready; infer_instance

inductive Status where
  | jointComplete | exhausted | observationCut
  deriving DecidableEq
structure Result where
  state : State model
  status : Status
  inputs : List (InterferenceEnvelope.Input model.source.code)

def finish (past : Stages model) (pending : List (Rule model.source.code)) : Result model :=
  let state := audit model past pending
  ⟨state, if Ready model start vocabulary encoding law state then .jointComplete
    else if UnifiedResponse.fuel model start past = 0 then .exhausted else .observationCut, []⟩

def after (past : Stages model) (rule : Rule model.source.code) (move : Move model.source.code) : Stages model :=
  past ++ [(rule, EventStep.fixed move)]

-- Only the source's physical clock may stop execution. Global completion and
-- the responsibility audit never select a rule, cancel a tail, or pick a phase.
def execute : List (Rule model.source.code) → Stages model → Opponent model.source.code → Result model
  | [], past, _ => finish model start vocabulary encoding law past []
  | rule :: tail, past, rival =>
    if UnifiedResponse.fuel model start past = 0 then finish model start vocabulary encoding law past (rule :: tail)
    else
      let input := InterferenceEnvelope.observe start past allowance rival
      let next := execute tail (after model past rule input.admitted) rival
      ⟨next.state, next.status, input :: next.inputs⟩

def guarantees : List (Rule model.source.code) → Stages model → Bool
  | [], past => decide (Ready model start vocabulary encoding law (audit model past []))
  | rule :: tail, past =>
    if UnifiedResponse.fuel model start past = 0 then false
    else (InterferenceEnvelope.choices start past allowance).all fun move => guarantees tail (after model past rule move)

def seeded (_start : Cursor model.source.code)
    (_vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (_encoding : StageTransport.Encoding (code := model.source.code)) (_law : StageReception.Law model.source.code)
    (past : Stages model) := audit model past []
def plan (past : Stages model) := LocalWindowPlan.produce vocabulary encoding law start (past.map Prod.fst)
def guaranteed (past : Stages model) := guarantees model start vocabulary encoding law allowance
  (plan model start vocabulary encoding law (seeded model start vocabulary encoding law past).past)
  (seeded model start vocabulary encoding law past).past
def produce (past : Stages model) (rival : Opponent model.source.code) := execute model start vocabulary encoding law allowance
  (plan model start vocabulary encoding law (seeded model start vocabulary encoding law past).past)
  (seeded model start vocabulary encoding law past).past rival

theorem every_actual_prefix_is_in_the_complete_snapshot_audit (entry past : Stages model)
    (actual : entry <+: past) : entry ∈ snapshots model past := by
  obtain ⟨suffix, rfl⟩ := actual
  apply List.mem_map.mpr
  refine ⟨entry.length, List.mem_range.mpr (by simp only [List.length_append]; omega), ?_⟩
  simp

private theorem finish_success (past : Stages model) (pending : List (Rule model.source.code))
    (accepted : (finish model start vocabulary encoding law past pending).status = .jointComplete) :
    Ready model start vocabulary encoding law (finish model start vocabulary encoding law past pending).state := by
  unfold finish at accepted ⊢
  dsimp only at accepted ⊢
  split_ifs at accepted with complete
  exact complete

theorem success_keeps_the_entire_original_goal (programme : List (Rule model.source.code)) (past : Stages model)
    (rival : Opponent model.source.code)
    (accepted : (execute model start vocabulary encoding law allowance programme past rival).status = .jointComplete) :
    Ready model start vocabulary encoding law (execute model start vocabulary encoding law allowance programme past rival).state := by
  induction programme generalizing past with
  | nil => exact finish_success model start vocabulary encoding law past [] accepted
  | cons rule tail ih =>
    simp only [execute] at accepted ⊢
    split_ifs at accepted ⊢ with stopped
    · exact finish_success model start vocabulary encoding law past (rule :: tail) accepted
    · exact ih _ accepted

theorem every_compliant_actual_callback_completes (programme : List (Rule model.source.code)) (past : Stages model)
    (rival : Opponent model.source.code)
    (certified : guarantees model start vocabulary encoding law allowance programme past = true)
    (compliant : ((execute model start vocabulary encoding law allowance programme past rival).inputs.all fun input => input.within) = true) :
    (execute model start vocabulary encoding law allowance programme past rival).status = .jointComplete := by
  induction programme generalizing past with
  | nil =>
    have complete := of_decide_eq_true certified
    simp only [execute, finish, if_pos complete]
  | cons rule tail ih =>
    by_cases stopped : UnifiedResponse.fuel model start past = 0
    · simp only [guarantees, if_pos stopped] at certified; contradiction
    · simp only [guarantees, if_neg stopped] at certified
      simp only [execute, if_neg stopped, List.all_cons, Bool.and_eq_true] at compliant ⊢
      have supported := of_decide_eq_true compliant.1
      exact ih _ (List.all_eq_true.mp certified _ supported) compliant.2

theorem execution_keeps_the_actual_history_and_physical_bound
    (programme : List (Rule model.source.code)) (past : Stages model) (rival : Opponent model.source.code) :
    past <+: (execute model start vocabulary encoding law allowance programme past rival).state.past ∧
    (execute model start vocabulary encoding law allowance programme past rival).state.past.length ≤ past.length + programme.length := by
  induction programme generalizing past with
  | nil => exact ⟨List.prefix_refl _, Nat.le_refl _⟩
  | cons rule tail ih =>
    simp only [execute]
    split
    · exact ⟨List.prefix_refl _, by simp only [finish, audit]; omega⟩
    · have rest := ih (after model past rule (InterferenceEnvelope.observe start past allowance rival).admitted)
      refine ⟨(List.prefix_append _ _).trans rest.1, ?_⟩
      have count := rest.2
      simp only [after, List.length_append, List.length_singleton] at count
      simpa only [after, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using count

theorem every_executed_state_keeps_the_entire_actual_snapshot_inventory
    (programme : List (Rule model.source.code)) (past : Stages model) (rival : Opponent model.source.code) :
    (execute model start vocabulary encoding law allowance programme past rival).state.batches =
      snapshots model (execute model start vocabulary encoding law allowance programme past rival).state.past := by
  induction programme generalizing past with
  | nil => rfl
  | cons rule tail ih =>
    simp only [execute]
    split
    · rfl
    · exact ih _

theorem compliant_execution_preserves_one_source_deviation_budget
    (programme : List (Rule model.source.code)) (past : Stages model) (rival : Opponent model.source.code)
    (compliant : ((execute model start vocabulary encoding law allowance programme past rival).inputs.all fun input => input.within) = true) :
    InterferenceEnvelope.spent start (execute model start vocabulary encoding law allowance programme past rival).state.past ≤
      max model.source.code.eventLimit (InterferenceEnvelope.spent start past) := by
  induction programme generalizing past with
  | nil => exact Nat.le_max_right _ _
  | cons rule tail ih =>
    simp only [execute]
    split
    · exact Nat.le_max_right _ _
    · rename_i live
      simp only [execute, if_neg live, List.all_cons, Bool.and_eq_true] at compliant
      have edge := InterferenceEnvelope.a_supported_actual_step_preserves_the_source_interface_bound start past allowance rule
        (InterferenceEnvelope.observe start past allowance rival).admitted
        (InterferenceEnvelope.external_intake_is_idempotent _) (of_decide_eq_true compliant.1)
      have rest := ih _ compliant.2
      exact rest.trans (Nat.max_le.mpr ⟨Nat.le_max_left _ _, edge⟩)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalWindowRun
