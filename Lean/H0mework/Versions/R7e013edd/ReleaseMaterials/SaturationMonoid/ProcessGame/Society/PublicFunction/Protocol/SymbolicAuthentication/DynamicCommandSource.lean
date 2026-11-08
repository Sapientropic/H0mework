import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommandWindowSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DynamicCommandSource
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (delay : Nat)

abbrev State := LocalCommandRun.State model start
abbrev entry (state : State model start) (input : LocalCommandSource.Input) :=
  LocalCommandSource.observe model (state.current model start) input
abbrev intake (state : State model start) (input : LocalCommandSource.Input) :=
  InterferenceEnvelope.intake (state.current model start) (entry model start state input |>.stage model).2
-- This admits the actual communication callback; the original entry still records local signer/interface refusals.
def within (state : State model start) (input : LocalCommandSource.Input) : Bool :=
  decide (intake model start state input ∈ InterferenceEnvelope.choices start state.stages delay)
def menu (state : State model start) : List LocalCommandSource.Input :=
  (CommandWindowSource.menu model).filter (within model start delay state)

-- A rejected callback has already happened: its literal input and original row remain in `after`.
structure Refusal (state : State model start) (input : LocalCommandSource.Input) where
  private mk ::
  failed : within model start delay state input = false
abbrev Refusal.after {state : State model start} {input : LocalCommandSource.Input}
    (_refused : Refusal model start delay state input) := LocalCommandRun.step model start state input
inductive Submission (state : State model start) (input : LocalCommandSource.Input) where
  | admitted (allowed : within model start delay state input = true)
  | blocked (refused : Refusal model start delay state input)
def submit (state : State model start) (input : LocalCommandSource.Input) : Submission model start delay state input :=
  if allowed : within model start delay state input = true then .admitted allowed
  else .blocked ⟨Bool.eq_false_iff.mpr allowed⟩

theorem a_refusal_retains_the_actual_attempt_and_original_execution_row
    (state : State model start) (input : LocalCommandSource.Input)
    (refused : Refusal model start delay state input) :
    refused.after.inputs = state.inputs ++ [input] ∧
    refused.after.entries = state.entries ++ [entry model start state input] ∧
    refused.after.entries.map (LocalCommandSource.Entry.row model) = StageTrace.records start refused.after.stages :=
  ⟨(LocalCommandRun.every_step_retains_the_literal_attempt_and_its_actual_stage model start state input).1,
    rfl,refused.after.row_exact⟩

theorem actual_admission_is_exactly_the_original_prefix_timing_extension
    (state : State model start) (input : LocalCommandSource.Input) :
    AdaptiveRejectionHistory.Compliant start delay (LocalCommandRun.step model start state input).stages ↔
      AdaptiveRejectionHistory.Compliant start delay state.stages ∧ within model start delay state input = true := by
  let stage := (entry model start state input).stage model
  change AdaptiveRejectionHistory.Compliant start delay (state.stages ++ [stage]) ↔ _
  have last : InterferenceEnvelope.intake (EventHistory.execute start
      ((state.stages ++ [stage]).take state.stages.length))
      (AdaptiveRejectionHistory.rivals (state.stages ++ [stage]) state.stages.length) =
      intake model start state input := by
    simp [AdaptiveRejectionHistory.rivals,AdaptiveRejectionHistory.slot,stage]
  constructor
  · intro compliant
    refine ⟨InquiryControlConsumer.a_compliant_actual_extension_requires_its_original_prefix
      model start delay state.stages [stage] compliant,?_⟩
    have allowed := compliant state.stages.length (by simp)
    rw [last] at allowed
    simpa only [List.take_left,within,decide_eq_true_eq] using allowed
  · rintro ⟨before,allowed⟩ n bounded
    by_cases earlier : n < state.stages.length
    · have old := before n earlier
      simpa [AdaptiveRejectionHistory.rivals,AdaptiveRejectionHistory.slot,List.getElem?_append,
        earlier,List.take_append_of_le_length (Nat.le_of_lt earlier)] using old
    · have same : n = state.stages.length := by simp only [List.length_append,List.length_singleton] at bounded; omega
      subst n
      rw [last]
      simpa only [List.take_left,within,decide_eq_true_eq] using allowed

theorem refused_timing_cannot_be_laundered_by_a_later_suffix
    (state : State model start) (input : LocalCommandSource.Input)
    (refused : Refusal model start delay state input)
    (more : List (EventHistory.Stage (code := model.source.code))) :
    ¬ AdaptiveRejectionHistory.Compliant start delay (refused.after.stages ++ more) := by
  intro later
  have original := InquiryControlConsumer.a_compliant_actual_extension_requires_its_original_prefix
    model start delay refused.after.stages more later
  have accepted := (actual_admission_is_exactly_the_original_prefix_timing_extension model start delay state input).mp original
  rw [refused.failed] at accepted
  cases accepted.2

def advance (state : State model start) : List (State model start) :=
  (menu model start delay state).map (LocalCommandRun.step model start state)
def cases (state : State model start) : Nat → List (State model start) :=
  Nat.rec [state] (fun _ previous => previous.flatMap (advance model start delay))

theorem every_dynamic_branch_is_an_original_raw_execution
    (state branch : State model start) (count : Nat)
    (origin : branch ∈ cases model start delay state count) :
    branch ∈ CommandWindowSource.cases model start state count := by
  induction count generalizing branch with
  | zero => exact origin
  | succ count ih =>
    obtain ⟨before,member,next⟩ := List.mem_flatMap.mp origin
    obtain ⟨input,allowed,same⟩ := List.mem_map.mp next
    exact List.mem_flatMap.mpr ⟨before,ih before member,List.mem_map.mpr
      ⟨input,(List.mem_filter.mp allowed).1,same⟩⟩

theorem the_dynamic_source_generates_every_original_prefix_timing_condition
    (state branch : State model start) (count : Nat)
    (initial : AdaptiveRejectionHistory.Compliant start delay state.stages)
    (origin : branch ∈ cases model start delay state count) :
    AdaptiveRejectionHistory.Compliant start delay branch.stages := by
  induction count generalizing branch with
  | zero => cases List.mem_singleton.mp origin; exact initial
  | succ count ih =>
    obtain ⟨before,member,next⟩ := List.mem_flatMap.mp origin
    obtain ⟨input,allowed,same⟩ := List.mem_map.mp next
    rw [← same]
    exact (actual_admission_is_exactly_the_original_prefix_timing_extension model start delay before input).mpr
      ⟨ih before member,(List.mem_filter.mp allowed).2⟩

-- Raw policies are total even when the generated domain is empty or an attempted move is refused.
structure Failure where
  private mk ::
  before : State model start
  input : LocalCommandSource.Input
  refused : Refusal model start delay before input
inductive Outcome where
  | running (state : State model start)
  | blocked (failure : Failure model start delay)
def Outcome.history : Outcome model start delay → State model start
  | .running state => state
  | .blocked failure => failure.refused.after
def tick (choose : Nat → State model start → LocalCommandSource.Input) (index : Nat) :
    Outcome model start delay → Outcome model start delay
  | .blocked failure => .blocked failure
  | .running state => match submit model start delay state (choose index state) with
    | .admitted _ => .running (LocalCommandRun.step model start state (choose index state))
    | .blocked refused => .blocked ⟨state,choose index state,refused⟩
def actual (choose : Nat → State model start → LocalCommandSource.Input) (state : State model start) :
    Nat → Outcome model start delay :=
  Nat.rec (.running state) (tick model start delay choose)

theorem every_running_adaptive_execution_has_its_generated_source_branch
    (choose : Nat → State model start → LocalCommandSource.Input)
    (state branch : State model start) (count : Nat)
    (inside : ∀ index before, choose index before ∈ CommandWindowSource.menu model)
    (running : actual model start delay choose state count = .running branch) :
    branch ∈ cases model start delay state count := by
  induction count generalizing branch with
  | zero => cases Outcome.running.inj running; exact List.mem_singleton_self _
  | succ count ih =>
    change tick model start delay choose count (actual model start delay choose state count) = .running branch at running
    cases previous : actual model start delay choose state count with
    | blocked failure => simp only [previous,tick] at running; contradiction
    | running before =>
      rw [previous] at running
      cases decision : submit model start delay before (choose count before) with
      | admitted allowed =>
        simp only [tick,decision] at running
        cases Outcome.running.inj running
        exact List.mem_flatMap.mpr ⟨before,ih before previous,List.mem_map.mpr
          ⟨choose count before,List.mem_filter.mpr ⟨inside count before,allowed⟩,rfl⟩⟩
      | blocked refused => simp only [tick,decision] at running; contradiction

theorem every_blocked_adaptive_execution_retains_its_actual_failed_source_branch
    (choose : Nat → State model start → LocalCommandSource.Input)
    (state : State model start) (count : Nat) (failure : Failure model start delay)
    (inside : ∀ index before, choose index before ∈ CommandWindowSource.menu model)
    (blocked : actual model start delay choose state count = .blocked failure) :
    ∃ depth < count, failure.before ∈ cases model start delay state depth ∧
      failure.input = choose depth failure.before ∧
      failure.refused.after ∈ CommandWindowSource.cases model start state (depth+1) := by
  induction count with
  | zero => contradiction
  | succ count ih =>
    change tick model start delay choose count (actual model start delay choose state count) = .blocked failure at blocked
    cases previous : actual model start delay choose state count with
    | blocked earlier =>
      simp only [previous,tick] at blocked
      cases Outcome.blocked.inj blocked
      obtain ⟨depth,bounded,rest⟩ := ih previous
      exact ⟨depth,by omega,rest⟩
    | running before =>
      rw [previous] at blocked
      cases decision : submit model start delay before (choose count before) with
      | admitted allowed => simp only [tick,decision] at blocked; contradiction
      | blocked refused =>
        simp only [tick,decision] at blocked
        cases Outcome.blocked.inj blocked
        have origin := every_running_adaptive_execution_has_its_generated_source_branch
          model start delay choose state before count inside previous
        refine ⟨count,by omega,origin,rfl,?_⟩
        exact List.mem_flatMap.mpr ⟨before,every_dynamic_branch_is_an_original_raw_execution
          model start delay state before count origin,List.mem_map.mpr ⟨choose count before,inside count before,rfl⟩⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DynamicCommandSource
