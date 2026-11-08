import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryControlSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryControlConsumer
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

abbrev Stages := JointResponse.Stages model
abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
abbrev width := SourceClockTermination.width model start
abbrev cases := InquiryControlSource.cases model start delay

def active (past : Stages model) (controls first window : Nat) : List (Stages model) :=
  (cases model start delay past controls).filter fun branch => decide
    (¬ JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law branch (first+window)))

def windows (past : Stages model) (controls : Nat) (branch : Stages model) : Bool :=
  (List.range (SourceClockTermination.blocks model start branch)).all fun block =>
    if JointResponse.Clear model start vocabulary encoding law
      (atCut model start vocabulary encoding law branch ((block+1)*width model start)) then true else
    ControlServiceEnvelope.Budget.check model start vocabulary encoding law
      (active model start vocabulary encoding law delay past controls (block*width model start) (width model start))
      (block*width model start) (width model start)

def reserve (branch : Stages model) : Bool := decide
  (SourceClockTermination.deadline model start branch * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start branch)
def timing (branch : Stages model) : Bool := AdaptiveRejectionHistory.check start delay
  (UnifiedRecoveryRun.run model start vocabulary encoding law (SourceClockTermination.deadline model start branch) branch).stages
def preflight (past : Stages model) (controls : Nat) (branch : Stages model) : Bool :=
  reserve model start branch && (timing model start vocabulary encoding law delay branch &&
    windows model start vocabulary encoding law delay past controls branch)
def check (past : Stages model) (controls : Nat) : Bool :=
  decide (0 < width model start) && (cases model start delay past controls).all (preflight model start vocabulary encoding law delay past controls)

structure Covered (past : Stages model) (controls : Nat) where
  private mk ::
  checked : check model start vocabulary encoding law delay past controls = true
structure Refusal (past : Stages model) (controls : Nat) where
  private mk ::
  branch : Stages model
  origin : branch ∈ cases model start delay past controls
  failed : preflight model start vocabulary encoding law delay past controls branch ≠ true
inductive Obstruction where
  | sourceFuel | sourceTiming | serviceWindow
  deriving DecidableEq
def Refusal.reason {past : Stages model} {controls : Nat}
    (refused : Refusal model start vocabulary encoding law delay past controls) : Obstruction :=
  if reserve model start refused.branch = false then .sourceFuel else
  if timing model start vocabulary encoding law delay refused.branch = false then .sourceTiming else .serviceWindow

inductive Result (past : Stages model) (controls : Nat) where
  | covered (source : Covered model start vocabulary encoding law delay past controls)
  | noRoster
  | blocked (refused : Refusal model start vocabulary encoding law delay past controls)

def produce (past : Stages model) (controls : Nat) : Result model start vocabulary encoding law delay past controls :=
  if roster : 0 < width model start then
    match inspect (fun branch => preflight model start vocabulary encoding law delay past controls branch = true)
      (cases model start delay past controls) with
    | .accepted checked => .covered ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true roster,List.all_eq_true.mpr checked⟩⟩
    | .rejected branch origin failed => .blocked ⟨branch,origin,failed⟩
  else .noRoster

theorem a_computed_source_check_returns_its_own_success (past : Stages model) (controls : Nat)
    (checked : check model start vocabulary encoding law delay past controls = true) :
    ∃ source, produce model start vocabulary encoding law delay past controls = .covered source := by
  have split := Bool.and_eq_true_iff.mp checked
  unfold produce
  rw [dif_pos (of_decide_eq_true split.1)]
  cases scanned : inspect (fun branch => preflight model start vocabulary encoding law delay past controls branch = true)
      (cases model start delay past controls) with
  | accepted good => exact ⟨_,rfl⟩
  | rejected branch origin failed => exact False.elim (failed (List.all_eq_true.mp split.2 branch origin))

theorem one_actual_failed_branch_forces_an_executable_refusal
    (past : Stages model) (controls : Nat) (branch : Stages model)
    (roster : 0 < width model start)
    (origin : branch ∈ cases model start delay past controls)
    (failed : preflight model start vocabulary encoding law delay past controls branch = false) :
    ∃ refused, produce model start vocabulary encoding law delay past controls = .blocked refused := by
  unfold produce
  rw [dif_pos roster]
  cases scan : inspect (fun branch => preflight model start vocabulary encoding law delay past controls branch = true)
      (cases model start delay past controls) with
  | accepted checked =>
    have impossible := checked branch origin
    rw [failed] at impossible
    cases impossible
  | rejected rejected origin failure => exact ⟨_,rfl⟩

theorem the_computed_refusal_is_an_executable_source_counterexample
    (past : Stages model) (controls : Nat) (refused : Refusal model start vocabulary encoding law delay past controls) :
    past <+: refused.branch ∧ refused.branch.length = past.length+controls ∧
    preflight model start vocabulary encoding law delay past controls refused.branch = false := by
  have original := InquiryControlSource.generated_branches_keep_the_original_prefix_and_pay_each_control_stage
    model start delay past refused.branch controls refused.origin
  refine ⟨original.1,original.2,?_⟩
  cases observed : preflight model start vocabulary encoding law delay past controls refused.branch
  · rfl
  · exact False.elim (refused.failed observed)

theorem the_source_window_scan_generates_actual_identity_availability
    (past : Stages model) (controls : Nat) (branch : Stages model)
    (origin : branch ∈ cases model start delay past controls)
    (checked : windows model start vocabulary encoding law delay past controls branch = true) :
    ServiceActorWindow.Available model start vocabulary encoding law (SourceClockTermination.blocks model start branch) branch := by
  intro block bounded unfinished
  have scanned := List.all_eq_true.mp checked block (List.mem_range.mpr bounded)
  simp only [if_neg unfinished] at scanned
  have member : branch ∈ active model start vocabulary encoding law delay past controls
      (block*width model start) (width model start) := by
    apply List.mem_filter.mpr
    refine ⟨origin,?_⟩
    have same : block*width model start+width model start = (block+1)*width model start := by rw [Nat.add_mul,Nat.one_mul]
    simpa only [same,decide_eq_true_eq] using unfinished
  refine ⟨ControlServiceEnvelope.Budget.a_checked_source_budget_generates_each_actual_surplus
    model start vocabulary encoding law _ _ _ scanned branch member,?_⟩
  intro offset within stillOpen
  exact ControlServiceEnvelope.Budget.a_checked_source_domain_generates_each_actual_communication_gate
    model start vocabulary encoding law _ _ _ scanned branch member offset within stillOpen

theorem source_generated_legal_control_and_identity_budget_force_original_joint_completion
    (past : Stages model) (controls : Nat) (source : Covered model start vocabulary encoding law delay past controls)
    (choose : Nat → (past : Stages model) → InquiryControlSource.Command model start delay past) :
    let actual := InquiryControlSource.actual model start delay choose past controls
    (UnifiedRecoveryRun.produce model start vocabulary encoding law actual).status = .jointComplete ∧
    (UnifiedRecoveryRun.produce model start vocabulary encoding law actual).stages.length ≤ actual.length+
      SourceClockTermination.deadline model start actual*CommunicationWorkBudget.slotAllowance model start := by
  have origin := InquiryControlSource.every_actual_adaptive_source_selection_is_in_the_original_generated_domain model start delay choose past controls
  have checked := Bool.and_eq_true_iff.mp source.checked
  have actual := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked.2 _ origin)
  have history := Bool.and_eq_true_iff.mp actual.2
  exact ServiceActorWindow.source_generated_identity_availability_forces_the_original_joint_completion
    model start vocabulary encoding law _ delay (of_decide_eq_true checked.1) (of_decide_eq_true actual.1)
    (the_source_window_scan_generates_actual_identity_availability model start vocabulary encoding law delay past controls _ origin history.2)
    ((AdaptiveRejectionHistory.check_iff start delay _).mp history.1)

theorem a_completed_actual_branch_disposes_its_later_window_obligations
    (past : Stages model) (controls rounds : Nat) (branch : Stages model)
    (room : rounds ≤ width model start)
    (completed : (UnifiedRecoveryRun.run model start vocabulary encoding law rounds branch).status = .jointComplete) :
    windows model start vocabulary encoding law delay past controls branch = true := by
  apply List.all_eq_true.mpr
  intro block _
  have closed := UnifiedRecoveryRun.completion_contains_all_original_joint_gates model start vocabulary encoding law
    rounds branch completed
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

theorem the_same_actual_source_consumes_native_rows_history_receipts_whole_ledger_and_next
    (past : Stages model) (controls : Nat)
    (source : Covered model start vocabulary encoding law delay past controls)
    (choose : Nat → (past : Stages model) → InquiryControlSource.Command model start delay past) :
    let full := (UnifiedRecoveryRun.produce model start vocabulary encoding law (InquiryControlSource.actual model start delay choose past controls)).stages
    let final := EventHistory.execute start full
    let runtime := WithdrawalInquiryRuntime.runtime model final
    JointResponse.Clear model start vocabulary encoding law full ∧
    (∀ row ∈ (WithdrawalInquiryRuntime.authority model final).current.challenges,
      row.2.isPending (WithdrawalInquiryRuntime.family model final) (WithdrawalInquiryRuntime.sourceIndex model final) = false) ∧
    (InquiryControlSource.actual model start delay choose past controls) <+: full ∧
    StageAccountability.ledger start vocabulary encoding law (InquiryControlSource.actual model start delay choose past controls) <+: StageAccountability.ledger start vocabulary encoding law full ∧
    (∀ receiver, (StageReception.run vocabulary encoding law start (InquiryControlSource.actual model start delay choose past controls) receiver (InquiryControlSource.actual model start delay choose past controls).length).receipts <+:
      (StageReception.run vocabulary encoding law start full receiver full.length).receipts) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  have inside := InquiryControlSource.every_actual_adaptive_source_selection_is_in_the_original_generated_domain
    model start delay choose past controls
  have checked := Bool.and_eq_true_iff.mp source.checked
  have actual := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked.2 _ inside)
  have history := Bool.and_eq_true_iff.mp actual.2
  exact ServiceActorConsumer.the_generated_identity_window_is_consumed_by_the_original_root
    model start vocabulary encoding law _ delay (of_decide_eq_true checked.1) (of_decide_eq_true actual.1)
    (the_source_window_scan_generates_actual_identity_availability model start vocabulary encoding law delay past controls _ inside history.2)
    ((AdaptiveRejectionHistory.check_iff start delay _).mp history.1)

theorem a_compliant_actual_extension_requires_its_original_prefix
    (past more : Stages model)
    (compliant : AdaptiveRejectionHistory.Compliant start delay (past ++ more)) :
    AdaptiveRejectionHistory.Compliant start delay past := by
  intro index bounded
  have here := compliant index (by simp only [List.length_append]; omega)
  simpa [AdaptiveRejectionHistory.rivals,AdaptiveRejectionHistory.slot,List.getElem?_append,
    List.take_append_of_le_length (Nat.le_of_lt bounded),bounded] using here

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryControlConsumer
