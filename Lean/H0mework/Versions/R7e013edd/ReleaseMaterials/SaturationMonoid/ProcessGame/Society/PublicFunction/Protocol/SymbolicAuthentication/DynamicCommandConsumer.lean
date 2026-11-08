import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DynamicCommandSource
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommandWindowConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DynamicCommandConsumer
open Distributed Reaction Reaction.Feedback
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
  (delay : Nat)

abbrev State := LocalCommandRun.State model start
abbrev cases := DynamicCommandSource.cases model start delay
abbrev brief := CommandWindowConsumer.brief model start vocabulary encoding law delay

def nodes (state : State model start) (count : Nat) : List (State model start) :=
  (List.range count).flatMap (cases model start delay state)
def check (state : State model start) (count : Nat) : Bool :=
  AdaptiveRejectionHistory.check start delay state.stages &&
    ((nodes model start delay state count).all (fun before => !(DynamicCommandSource.menu model start delay before).isEmpty) &&
      (cases model start delay state count).all (brief model start vocabulary encoding law delay))
structure Covered (state : State model start) (count : Nat) where
  private mk ::
  checked : check model start vocabulary encoding law delay state count = true
inductive Obstruction (state : State model start) (count : Nat) where
  | inheritedTiming (failed : AdaptiveRejectionHistory.check start delay state.stages ≠ true)
  | noContinuation (before : State model start) (origin : before ∈ nodes model start delay state count)
      (empty : DynamicCommandSource.menu model start delay before = [])
  | noJointCompletion (branch : State model start) (origin : branch ∈ cases model start delay state count)
      (failed : brief model start vocabulary encoding law delay branch ≠ true)
inductive Result (state : State model start) (count : Nat) where
  | covered (source : Covered model start vocabulary encoding law delay state count)
  | blocked (obstruction : Obstruction model start vocabulary encoding law delay state count)

-- The internal-node scan is essential: an empty dynamic frontier cannot certify liveness by an empty `all`.
def produce (state : State model start) (count : Nat) : Result model start vocabulary encoding law delay state count :=
  if initial : AdaptiveRejectionHistory.check start delay state.stages = true then
    match inspect (fun before => DynamicCommandSource.menu model start delay before ≠ [])
        (nodes model start delay state count) with
    | .rejected before origin empty => .blocked (.noContinuation before origin (Decidable.byContradiction empty))
    | .accepted nonempty =>
      match inspect (fun branch => brief model start vocabulary encoding law delay branch = true)
          (cases model start delay state count) with
      | .rejected branch origin failed => .blocked (.noJointCompletion branch origin failed)
      | .accepted finished => .covered ⟨Bool.and_eq_true_iff.mpr ⟨initial,Bool.and_eq_true_iff.mpr
          ⟨List.all_eq_true.mpr (by simpa only [Bool.not_eq_true',List.isEmpty_eq_false_iff] using nonempty),
            List.all_eq_true.mpr finished⟩⟩⟩
  else .blocked (.inheritedTiming initial)

theorem a_computed_check_returns_its_own_coverage (state : State model start) (count : Nat)
    (checked : check model start vocabulary encoding law delay state count = true) :
    ∃ source, produce model start vocabulary encoding law delay state count = .covered source := by
  have parts := Bool.and_eq_true_iff.mp checked
  have scans := Bool.and_eq_true_iff.mp parts.2
  unfold produce
  rw [dif_pos parts.1]
  cases first : inspect (fun before => DynamicCommandSource.menu model start delay before ≠ [])
      (nodes model start delay state count) with
  | rejected before origin empty =>
    have nonempty := List.all_eq_true.mp scans.1 before origin
    exact False.elim (empty (by simpa only [Bool.not_eq_true',List.isEmpty_eq_false_iff] using nonempty))
  | accepted nonempty =>
    cases last : inspect (fun branch => brief model start vocabulary encoding law delay branch = true)
        (cases model start delay state count) with
    | rejected branch origin failed => exact False.elim (failed (List.all_eq_true.mp scans.2 branch origin))
    | accepted complete => exact ⟨_,rfl⟩

theorem a_covered_dynamic_domain_has_a_real_execution (state : State model start) (count : Nat)
    (source : Covered model start vocabulary encoding law delay state count) :
    ∃ branch, branch ∈ cases model start delay state count := by
  have live := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp source.checked).2).1
  have each : ∀ depth < count, ∀ before ∈ cases model start delay state depth,
      DynamicCommandSource.menu model start delay before ≠ [] := by
    intro depth bounded before origin
    have scanned := List.all_eq_true.mp live before (List.mem_flatMap.mpr ⟨depth,List.mem_range.mpr bounded,origin⟩)
    simpa only [Bool.not_eq_true',List.isEmpty_eq_false_iff] using scanned
  have reaches : ∀ depth ≤ count, ∃ branch, branch ∈ cases model start delay state depth := by
    intro depth bounded
    induction depth with
    | zero => exact ⟨state,List.mem_singleton_self _⟩
    | succ depth ih =>
      obtain ⟨before,origin⟩ := ih (by omega)
      obtain ⟨input,member⟩ := List.exists_mem_of_ne_nil _ (each depth (by omega) before origin)
      exact ⟨LocalCommandRun.step model start before input,List.mem_flatMap.mpr
        ⟨before,origin,List.mem_map.mpr ⟨input,member,rfl⟩⟩⟩
  exact reaches count (Nat.le_refl _)

theorem the_source_generates_the_affected_identity_budget_at_every_horizon
    (branch : State model start) (count : Nat)
    (origin : branch ∈ cases model start delay (LocalCommandRun.initial model start) count) :
    (AdaptiveRejectionInventory.identities start vocabulary encoding law branch.stages).card ≤
      AdaptiveReceptionBudget.capacity (code := model.source.code) := by
  apply AdaptiveRejectionHistory.the_actual_history_generates_its_own_rejection_capacity
    start vocabulary encoding law delay branch.stages
  exact DynamicCommandSource.the_dynamic_source_generates_every_original_prefix_timing_condition
    model start delay _ branch count (by intro n bounded; simp [LocalCommandRun.initial] at bounded) origin

theorem coverage_generates_original_joint_completion
    (state branch : State model start) (count : Nat)
    (source : Covered model start vocabulary encoding law delay state count)
    (origin : branch ∈ cases model start delay state count) :
    (UnifiedRecoveryRun.produce model start vocabulary encoding law branch.stages).status = .jointComplete := by
  have checked := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp source.checked).2).2 branch origin
  have first := Bool.and_eq_true_iff.mp checked
  have finish := Bool.and_eq_true_iff.mp first.2
  exact (UnifiedRunPrefix.completed_prefix_is_the_same_full_source_run model start vocabulary encoding law
    (SourceClockTermination.width model start) _ (of_decide_eq_true first.1) (of_decide_eq_true finish.1)).2

theorem dynamic_completion_consumes_original_responsibilities_receipts_whole_ledger_and_next
    (state branch : State model start) (count : Nat)
    (source : Covered model start vocabulary encoding law delay state count)
    (origin : branch ∈ cases model start delay state count) :
    let full := (UnifiedRecoveryRun.produce model start vocabulary encoding law branch.stages).stages
    let final := EventHistory.execute start full
    let runtime := WithdrawalInquiryRuntime.runtime model final
    JointResponse.Clear model start vocabulary encoding law full ∧
    (∀ row ∈ (WithdrawalInquiryRuntime.authority model final).current.challenges,
      row.2.isPending (WithdrawalInquiryRuntime.family model final) (WithdrawalInquiryRuntime.sourceIndex model final) = false) ∧
    branch.stages <+: full ∧
    StageAccountability.ledger start vocabulary encoding law branch.stages <+: StageAccountability.ledger start vocabulary encoding law full ∧
    (∀ receiver, (StageReception.run vocabulary encoding law start branch.stages receiver branch.stages.length).receipts <+:
      (StageReception.run vocabulary encoding law start full receiver full.length).receipts) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have complete := coverage_generates_original_joint_completion model start vocabulary encoding law delay state branch count source origin
  have closed := UnifiedRecoveryRun.completion_contains_all_original_joint_gates model start vocabulary encoding law _ _ complete
  have native := UnifiedRecoveryConsumer.actual_joint_completion_closes_the_entire_final_root_native_inventory
    model start vocabulary encoding law _ complete
  have rooted := UnifiedRecoveryConsumer.the_complete_actual_execution_preserves_incidents_receipts_all_native_histories_ledger_and_next
    model start vocabulary encoding law branch.stages
  exact ⟨closed,native,rooted.1,rooted.2.1,rooted.2.2.1,rooted.2.2.2.2.1,rooted.2.2.2.2.2⟩

theorem every_raw_adaptive_policy_returns_joint_completion_or_a_recorded_refused_callback
    (state : State model start) (count : Nat)
    (source : Covered model start vocabulary encoding law delay state count)
    (choose : Nat → State model start → LocalCommandSource.Input)
    (inside : ∀ index before, choose index before ∈ CommandWindowSource.menu model) :
    match DynamicCommandSource.actual model start delay choose state count with
    | .running branch => (UnifiedRecoveryRun.produce model start vocabulary encoding law branch.stages).status = .jointComplete
    | .blocked failure =>
      (∃ depth < count, failure.refused.after ∈ CommandWindowSource.cases model start state (depth+1)) ∧
      failure.refused.after.inputs = failure.before.inputs ++ [failure.input] ∧
      failure.refused.after.entries.map (LocalCommandSource.Entry.row model) = StageTrace.records start failure.refused.after.stages ∧
      ¬ AdaptiveRejectionHistory.Compliant start delay failure.refused.after.stages := by
  cases actual : DynamicCommandSource.actual model start delay choose state count with
  | running branch =>
    exact coverage_generates_original_joint_completion model start vocabulary encoding law delay state branch count source
      (DynamicCommandSource.every_running_adaptive_execution_has_its_generated_source_branch
        model start delay choose state branch count inside actual)
  | blocked failure =>
    obtain ⟨depth,bounded,_,_,origin⟩ := DynamicCommandSource.every_blocked_adaptive_execution_retains_its_actual_failed_source_branch
      model start delay choose state count failure inside actual
    have recorded := DynamicCommandSource.a_refusal_retains_the_actual_attempt_and_original_execution_row
      model start delay failure.before failure.input failure.refused
    refine ⟨⟨depth,bounded,origin⟩,recorded.1,recorded.2.2,?_⟩
    simpa only [List.append_nil] using DynamicCommandSource.refused_timing_cannot_be_laundered_by_a_later_suffix
      model start delay failure.before failure.input failure.refused []

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DynamicCommandConsumer
