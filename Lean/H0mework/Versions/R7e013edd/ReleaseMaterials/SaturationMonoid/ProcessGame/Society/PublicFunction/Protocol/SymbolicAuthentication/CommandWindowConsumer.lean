import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommandWindowSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommandWindowConsumer
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
abbrev Stages := JointResponse.Stages model
abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
abbrev width := SourceClockTermination.width model start
abbrev reserve := InquiryControlConsumer.reserve model start
abbrev timing := InquiryControlConsumer.timing model start vocabulary encoding law delay

def active (state : State model start) (controls first window : Nat) :=
  (CommandWindowSource.branches model start state controls).filter fun branch => decide
    (¬ JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law branch (first+window)))
def windows (state : State model start) (controls : Nat) (branch : Stages model) : Bool :=
  (List.range (SourceClockTermination.blocks model start branch)).all fun block =>
    if JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law branch ((block+1)*width model start)) then true else
    ControlServiceEnvelope.Budget.check model start vocabulary encoding law
      (active model start vocabulary encoding law state controls (block*width model start) (width model start))
      (block*width model start) (width model start)
def longCheck (state : State model start) (controls : Nat) (branch : State model start) : Bool :=
  reserve model start branch.stages && (timing model start vocabulary encoding law delay branch.stages &&
    windows model start vocabulary encoding law state controls branch.stages)
def brief (branch : State model start) : Bool :=
  decide (width model start ≤ JointResponse.fuel model start branch.stages) &&
    (decide ((UnifiedRecoveryRun.run model start vocabulary encoding law (width model start) branch.stages).status = .jointComplete) &&
      AdaptiveRejectionHistory.check start delay
        (UnifiedRecoveryRun.run model start vocabulary encoding law (width model start) branch.stages).stages)
def preflight (state : State model start) (controls : Nat) (branch : State model start) : Bool :=
  brief model start vocabulary encoding law delay branch || longCheck model start vocabulary encoding law delay state controls branch

def check (state : State model start) (controls : Nat) : Bool :=
  decide (0 < width model start) && (CommandWindowSource.cases model start state controls).all
    (preflight model start vocabulary encoding law delay state controls)

structure Covered (state : State model start) (controls : Nat) where
  private mk ::
  checked : check model start vocabulary encoding law delay state controls = true
structure Refusal (state : State model start) (controls : Nat) where
  private mk ::
  branch : State model start
  origin : branch ∈ CommandWindowSource.cases model start state controls
  failed : preflight model start vocabulary encoding law delay state controls branch ≠ true
inductive Obstruction where
  | sourceFuel | sourceTiming | serviceWindow
  deriving DecidableEq
def Refusal.reason {state : State model start} {controls : Nat}
    (refused : Refusal model start vocabulary encoding law delay state controls) : Obstruction :=
  if reserve model start refused.branch.stages = false then .sourceFuel else
  if timing model start vocabulary encoding law delay refused.branch.stages = false then .sourceTiming else .serviceWindow
inductive Result (state : State model start) (controls : Nat) where
  | covered (source : Covered model start vocabulary encoding law delay state controls)
  | noRoster
  | blocked (refused : Refusal model start vocabulary encoding law delay state controls)

def produce (state : State model start) (controls : Nat) : Result model start vocabulary encoding law delay state controls :=
  if roster : 0 < width model start then
    match inspect (fun branch => preflight model start vocabulary encoding law delay state controls branch = true)
      (CommandWindowSource.cases model start state controls) with
    | .accepted checked => .covered ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true roster,List.all_eq_true.mpr checked⟩⟩
    | .rejected branch origin failed => .blocked ⟨branch,origin,failed⟩
  else .noRoster

theorem a_computed_check_returns_its_own_coverage (state : State model start) (controls : Nat)
    (checked : check model start vocabulary encoding law delay state controls = true) :
    ∃ source, produce model start vocabulary encoding law delay state controls = .covered source := by
  have parts := Bool.and_eq_true_iff.mp checked
  unfold produce
  rw [dif_pos (of_decide_eq_true parts.1)]
  cases scanned : inspect (fun branch => preflight model start vocabulary encoding law delay state controls branch = true)
      (CommandWindowSource.cases model start state controls) with
  | accepted good => exact ⟨_,rfl⟩
  | rejected branch origin failed => exact False.elim (failed (List.all_eq_true.mp parts.2 branch origin))

theorem an_actual_failed_branch_forces_a_source_refusal
    (state : State model start) (controls : Nat) (branch : State model start)
    (positive : 0 < width model start)
    (origin : branch ∈ CommandWindowSource.cases model start state controls)
    (failed : preflight model start vocabulary encoding law delay state controls branch = false) :
    ∃ refused, produce model start vocabulary encoding law delay state controls = .blocked refused := by
  unfold produce
  rw [dif_pos positive]
  cases scan : inspect (fun branch => preflight model start vocabulary encoding law delay state controls branch = true)
      (CommandWindowSource.cases model start state controls) with
  | accepted checked =>
    have impossible := checked branch origin
    rw [failed] at impossible
    cases impossible
  | rejected rejected origin failure => exact ⟨_,rfl⟩

theorem a_refusal_preserves_the_actual_inputs_and_exact_failed_branch
    (state : State model start) (controls : Nat) (refused : Refusal model start vocabulary encoding law delay state controls) :
    state.entries <+: refused.branch.entries ∧ state.stages <+: refused.branch.stages ∧
      refused.branch.inputs.length = state.inputs.length + controls ∧
      preflight model start vocabulary encoding law delay state controls refused.branch = false := by
  have paid := CommandWindowSource.every_branch_keeps_its_literal_attempts_and_original_stages model start state refused.branch controls refused.origin
  refine ⟨paid.1,paid.2.1,paid.2.2.1,?_⟩
  cases actual : preflight model start vocabulary encoding law delay state controls refused.branch with
  | false => rfl
  | true => exact False.elim (refused.failed actual)

theorem an_actual_timing_failure_cannot_be_erased_by_later_completion
    (state : State model start) (controls : Nat) (branch : State model start)
    (failed : AdaptiveRejectionHistory.check start delay branch.stages = false) :
    preflight model start vocabulary encoding law delay state controls branch = false := by
  have extended (rounds : Nat) : AdaptiveRejectionHistory.check start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds branch.stages).stages = false := by
    cases observed : AdaptiveRejectionHistory.check start delay
        (UnifiedRecoveryRun.run model start vocabulary encoding law rounds branch.stages).stages with
    | false => rfl
    | true =>
      have compliant := (AdaptiveRejectionHistory.check_iff start delay _).mp observed
      obtain ⟨more,same⟩ := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history
        model start vocabulary encoding law rounds branch.stages
      rw [← same] at compliant
      have before := InquiryControlConsumer.a_compliant_actual_extension_requires_its_original_prefix
        model start delay branch.stages more compliant
      have impossible := (AdaptiveRejectionHistory.check_iff start delay _).mpr before
      rw [failed] at impossible
      cases impossible
  unfold preflight brief longCheck
  change ((_ && (_ && AdaptiveRejectionHistory.check start delay _)) ||
    (_ && (AdaptiveRejectionHistory.check start delay _ && _))) = false
  rw [extended,extended]
  simp only [Bool.and_false,Bool.false_and,Bool.or_false]

theorem the_source_window_check_generates_actual_identity_availability
    (state : State model start) (controls : Nat) (branch : State model start)
    (origin : branch ∈ CommandWindowSource.cases model start state controls)
    (checked : windows model start vocabulary encoding law state controls branch.stages = true) :
    ServiceActorWindow.Available model start vocabulary encoding law (SourceClockTermination.blocks model start branch.stages) branch.stages := by
  intro block bounded unfinished
  have scanned := List.all_eq_true.mp checked block (List.mem_range.mpr bounded)
  simp only [if_neg unfinished] at scanned
  have member : branch.stages ∈ active model start vocabulary encoding law state controls
      (block*width model start) (width model start) := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨branch,origin,rfl⟩,?_⟩
    have same : block*width model start+width model start = (block+1)*width model start := by rw [Nat.add_mul,Nat.one_mul]
    simpa only [same,decide_eq_true_eq] using unfinished
  refine ⟨ControlServiceEnvelope.Budget.a_checked_source_budget_generates_each_actual_surplus
    model start vocabulary encoding law _ _ _ scanned branch.stages member,?_⟩
  intro offset within stillOpen
  exact ControlServiceEnvelope.Budget.a_checked_source_domain_generates_each_actual_communication_gate
    model start vocabulary encoding law _ _ _ scanned branch.stages member offset within stillOpen

theorem completed_prefixes_dispose_their_later_service_windows
    (state : State model start) (controls rounds : Nat) (branch : Stages model)
    (room : rounds ≤ width model start)
    (completed : (UnifiedRecoveryRun.run model start vocabulary encoding law rounds branch).status = .jointComplete) :
    windows model start vocabulary encoding law state controls branch = true := by
  apply List.all_eq_true.mpr
  intro block _
  have closed := UnifiedRecoveryRun.completion_contains_all_original_joint_gates model start vocabulary encoding law rounds branch completed
  have enough : rounds ≤ (block+1)*width model start := by nlinarith
  have same := UnifiedRunPrefix.actual_run_prefixes_compose model start vocabulary encoding law rounds
    ((block+1)*width model start-rounds) branch
  rw [Nat.add_sub_of_le enough,
    UnifiedRunPrefix.a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law _ closed] at same
  have final : JointResponse.Clear model start vocabulary encoding law
      (atCut model start vocabulary encoding law branch ((block+1)*width model start)) := by
    change JointResponse.Clear model start vocabulary encoding law
      (UnifiedRunPrefix.atCut model start vocabulary encoding law branch ((block+1)*width model start))
    rw [same]
    exact closed
  exact if_pos final

theorem coverage_generates_actual_identity_availability
    (state : State model start) (controls : Nat) (source : Covered model start vocabulary encoding law delay state controls)
    (choose : Nat → State model start → CommandWindowSource.Command model) :
    let actual := CommandWindowSource.actual model start choose state controls
    ServiceActorWindow.Available model start vocabulary encoding law
      (SourceClockTermination.blocks model start actual.stages) actual.stages := by
  have origin := CommandWindowSource.every_actual_adaptive_input_has_its_source_branch model start choose state controls
  have checked := Bool.and_eq_true_iff.mp source.checked
  have accepted := Bool.or_eq_true_iff.mp (List.all_eq_true.mp checked.2 _ origin)
  apply the_source_window_check_generates_actual_identity_availability model start vocabulary encoding law state controls _ origin
  rcases accepted with early | later
  · have finish := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp early).2
    exact completed_prefixes_dispose_their_later_service_windows model start vocabulary encoding law state controls
      (width model start) _ (Nat.le_refl _) (of_decide_eq_true finish.1)
  · exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp later).2).2

theorem coverage_generates_joint_completion_for_every_adaptive_local_command
    (state : State model start) (controls : Nat) (source : Covered model start vocabulary encoding law delay state controls)
    (choose : Nat → State model start → CommandWindowSource.Command model) :
    let actual := CommandWindowSource.actual model start choose state controls
    (UnifiedRecoveryRun.produce model start vocabulary encoding law actual.stages).status = .jointComplete := by
  have origin := CommandWindowSource.every_actual_adaptive_input_has_its_source_branch model start choose state controls
  have checked := Bool.and_eq_true_iff.mp source.checked
  have accepted := Bool.or_eq_true_iff.mp (List.all_eq_true.mp checked.2 _ origin)
  rcases accepted with early | later
  · have first := Bool.and_eq_true_iff.mp early
    have finish := Bool.and_eq_true_iff.mp first.2
    exact (UnifiedRunPrefix.completed_prefix_is_the_same_full_source_run model start vocabulary encoding law
      (width model start) _ (of_decide_eq_true first.1) (of_decide_eq_true finish.1)).2
  · have actual := Bool.and_eq_true_iff.mp later
    have history := Bool.and_eq_true_iff.mp actual.2
    exact (ServiceActorWindow.source_generated_identity_availability_forces_the_original_joint_completion
      model start vocabulary encoding law _ delay (of_decide_eq_true checked.1) (of_decide_eq_true actual.1)
      (the_source_window_check_generates_actual_identity_availability model start vocabulary encoding law _ _ _ origin history.2)
      ((AdaptiveRejectionHistory.check_iff start delay _).mp history.1)).1

theorem the_same_source_consumes_original_responsibilities_receipts_whole_ledger_and_next
    (state : State model start) (controls : Nat) (source : Covered model start vocabulary encoding law delay state controls)
    (choose : Nat → State model start → CommandWindowSource.Command model) :
    let branch := CommandWindowSource.actual model start choose state controls
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
  have complete := coverage_generates_joint_completion_for_every_adaptive_local_command
    model start vocabulary encoding law delay state controls source choose
  have clear := UnifiedRecoveryRun.completion_contains_all_original_joint_gates model start vocabulary encoding law _ _ complete
  have native := UnifiedRecoveryConsumer.actual_joint_completion_closes_the_entire_final_root_native_inventory
    model start vocabulary encoding law _ complete
  have rooted := UnifiedRecoveryConsumer.the_complete_actual_execution_preserves_incidents_receipts_all_native_histories_ledger_and_next
    model start vocabulary encoding law (CommandWindowSource.actual model start choose state controls).stages
  exact ⟨clear,native,rooted.1,rooted.2.1,rooted.2.2.1,rooted.2.2.2.2.1,rooted.2.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommandWindowConsumer
