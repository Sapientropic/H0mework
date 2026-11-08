import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlServiceEnvelope

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlServiceConsumer
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

abbrev Stages := JointResponse.Stages model
abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
abbrev width := SourceClockTermination.width model start
abbrev Cases (past : Stages model) (controls : Nat) := DeliveryControlTree.branches controls past

theorem the_precontrol_envelope_generates_the_same_worker_for_each_actual_selected_path
    (past : Stages model) (controls first window : Nat) (pendingOnly : Bool)
    (source : ControlServiceEnvelope.Covered model start vocabulary encoding law past controls first window pendingOnly)
    (choose : Nat → DeliveryControlTree.Stages model.source.code → DeliveryControlTree.Command model.source.code)
    (index : Nat)
    (openCut : pendingOnly = true → ¬ JointResponse.Clear model start vocabulary encoding law
      (atCut model start vocabulary encoding law (DeliveryControlTree.run choose controls index past) (first+window))) :
    ∃ survivor, ServiceActorEnvelope.produce model start vocabulary encoding law
      (DeliveryControlTree.run choose controls index past) first window = .retained survivor := by
  have inside := ControlServiceEnvelope.an_actual_source_selector_belongs_to_its_covered_cases
    model start vocabulary encoding law past controls first window pendingOnly choose index openCut
  exact ServiceActorEnvelope.source_identity_surplus_forces_the_retained_branch model start vocabulary encoding law
    _ first window (ControlServiceEnvelope.Budget.a_checked_source_budget_generates_each_actual_surplus
      model start vocabulary encoding law _ first window source.checked _ inside)

private theorem a_quiet_control_installs_no_ballot_labels (cursor : Cursor model.source.code)
    (attempt : Move model.source.code) (worker : Fin model.source.code.sites) :
    StageBudget.labels vocabulary (StageTrace.material cursor SilentWindow.quiet (EventStep.fixed attempt)) worker = [] := by
  unfold StageBudget.labels Code.action
  split_ifs <;> rfl

private theorem a_quiet_control_issues_no_new_ballot (cursor : Cursor model.source.code)
    (attempt : Move model.source.code) :
    StageBudget.ledger vocabulary cursor [(SilentWindow.quiet,EventStep.fixed attempt)] = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro ballot member
  obtain ⟨row,inside,position,made⟩ := StageBudget.ledger_origin vocabulary cursor _ ballot member
  have word := StageBudget.issued_is_in_the_actual_installed_local_word vocabulary cursor _ row inside position ballot made
  have same : row = StageTrace.material cursor SilentWindow.quiet (EventStep.fixed attempt) := by
    simpa only [StageTrace.records,List.mem_cons,List.not_mem_nil,or_false] using inside
  rw [same,a_quiet_control_installs_no_ballot_labels model vocabulary cursor attempt ballot.key] at word
  exact List.not_mem_nil word.2.2

private theorem ledger_append (cursor : Cursor model.source.code) (left right : Stages model) :
    StageBudget.ledger vocabulary cursor (left ++ right) = StageBudget.ledger vocabulary cursor left ++
      StageBudget.ledger vocabulary (EventHistory.execute cursor left) right := by
  simp only [StageBudget.ledger,OriginQueue.records_append,List.flatMap_append]

theorem every_admitted_delivery_control_preserves_the_original_issued_ballot_ledger
    (past : Stages model) (controls : Nat) (branch : Stages model)
    (inside : branch ∈ Cases model past controls) :
    StageBudget.ledger vocabulary start branch = StageBudget.ledger vocabulary start past := by
  induction controls generalizing past with
  | zero => cases List.mem_singleton.mp inside; rfl
  | succ controls ih =>
    obtain ⟨attempt,_,member⟩ := List.mem_flatMap.mp inside
    rw [ih _ member]
    unfold DeliveryControlTree.advance
    rw [ledger_append model vocabulary,
      a_quiet_control_issues_no_new_ballot model vocabulary,List.append_nil]

def blocks (past : Stages model) (controls : Nat) :=
  (Cases model past controls).foldr (fun branch found => max (SourceClockTermination.blocks model start branch) found) 0

def windowsCheck (past : Stages model) (controls : Nat) : Bool :=
  (List.range (blocks model start past controls)).all fun block =>
    if (ControlServiceEnvelope.cases model start vocabulary encoding law past controls
      (block * width model start) (width model start) true).isEmpty then true else
    ControlServiceEnvelope.check model start vocabulary encoding law past controls
      (block * width model start) (width model start) true

def resourceCheck (past : Stages model) (controls : Nat) : Bool :=
  (Cases model past controls).all fun branch => decide
    (SourceClockTermination.deadline model start branch * CommunicationWorkBudget.slotAllowance model start <
      JointResponse.fuel model start branch)

def timingCheck (past : Stages model) (controls delay : Nat) : Bool :=
  (Cases model past controls).all fun branch => AdaptiveRejectionHistory.check start delay
    (UnifiedRecoveryRun.run model start vocabulary encoding law (SourceClockTermination.deadline model start branch) branch).stages

theorem an_actual_out_of_domain_callback_prevents_compliance_of_every_later_extension
    (past full : Stages model) (protocol : Rule model.source.code) (rival : Opponent model.source.code) (delay : Nat)
    (ordered : past ++ [(protocol,rival)] <+: full)
    (refused : InterferenceEnvelope.intake (EventHistory.execute start past) rival ∉
      InterferenceEnvelope.choices start past delay) :
    ¬ AdaptiveRejectionHistory.Compliant start delay full := by
  obtain ⟨tail,same⟩ := ordered
  rw [← same,List.append_assoc]
  intro compliant
  have here := compliant past.length (by simp only [List.length_append,List.length_cons]; omega)
  apply refused
  simpa [AdaptiveRejectionHistory.rivals,AdaptiveRejectionHistory.slot,List.getElem?_append] using here

def check (past : Stages model) (controls delay : Nat) : Bool :=
  decide (0 < width model start) && (resourceCheck model start past controls &&
    (timingCheck model start vocabulary encoding law past controls delay && windowsCheck model start vocabulary encoding law past controls))

theorem completed_source_branches_dispose_their_later_window_obligations
    (past : Stages model) (controls rounds : Nat)
    (room : rounds ≤ width model start)
    (completed : ∀ branch ∈ Cases model past controls,
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds branch).status = .jointComplete) :
    windowsCheck model start vocabulary encoding law past controls = true := by
  apply List.all_eq_true.mpr
  intro block _
  have empty : ControlServiceEnvelope.cases model start vocabulary encoding law past controls
      (block * width model start) (width model start) true = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro branch inside
    have closed := UnifiedRecoveryRun.completion_contains_all_original_joint_gates model start vocabulary encoding law
      rounds branch (completed branch inside)
    have enough : rounds ≤ block * width model start + width model start := by nlinarith
    have same := UnifiedRunPrefix.actual_run_prefixes_compose model start vocabulary encoding law rounds
      (block * width model start + width model start - rounds) branch
    rw [Nat.add_sub_of_le enough,
      UnifiedRunPrefix.a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law _ closed] at same
    have final : JointResponse.Clear model start vocabulary encoding law
        (atCut model start vocabulary encoding law branch (block * width model start + width model start)) := by
      change JointResponse.Clear model start vocabulary encoding law
        (UnifiedRunPrefix.atCut model start vocabulary encoding law branch (block * width model start + width model start))
      rw [same]
      exact closed
    simpa only [Bool.not_true,Bool.false_or,decide_eq_true_eq] using not_not_intro final
  simp only [empty,List.isEmpty_nil,if_true]

structure Covered (past : Stages model) (controls delay : Nat) where
  private mk ::
  checked : check model start vocabulary encoding law past controls delay = true

inductive Obstruction where
  | noRoster | sourceFuel | sourceTiming | sourceWindow
  deriving DecidableEq
inductive Result (past : Stages model) (controls delay : Nat) where
  | covered (source : Covered model start vocabulary encoding law past controls delay)
  | blocked (reason : Obstruction)

def produce (past : Stages model) (controls delay : Nat) : Result model start vocabulary encoding law past controls delay :=
  if checked : check model start vocabulary encoding law past controls delay = true then .covered ⟨checked⟩ else
  if width model start = 0 then .blocked .noRoster else
  if resourceCheck model start past controls = false then .blocked .sourceFuel else
  if timingCheck model start vocabulary encoding law past controls delay = false then .blocked .sourceTiming else
  .blocked .sourceWindow

theorem one_refused_actual_branch_forces_the_whole_source_timing_check_to_fail
    (past : Stages model) (controls delay : Nat) (branch : Stages model)
    (inside : branch ∈ Cases model past controls)
    (refused : ¬ AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law (SourceClockTermination.deadline model start branch) branch).stages) :
    timingCheck model start vocabulary encoding law past controls delay = false := by
  cases observed : timingCheck model start vocabulary encoding law past controls delay with
  | false => rfl
  | true =>
    exact False.elim (refused ((AdaptiveRejectionHistory.check_iff start delay _).mp
      (List.all_eq_true.mp observed branch inside)))

theorem intact_roster_and_reserve_with_failed_timing_return_the_precise_obstruction
    (past : Stages model) (controls delay : Nat)
    (roster : 0 < width model start)
    (reserve : resourceCheck model start past controls = true)
    (timing : timingCheck model start vocabulary encoding law past controls delay = false) :
    produce model start vocabulary encoding law past controls delay = .blocked .sourceTiming := by
  have failed : check model start vocabulary encoding law past controls delay = false := by
    unfold check
    rw [timing]
    simp only [Bool.false_and,Bool.and_false]
  unfold produce
  rw [dif_neg (by rw [failed]; decide),if_neg (by omega),reserve]
  simp only [Bool.true_eq_false,if_false,timing,if_true]

theorem a_successful_joint_source_check_returns_its_own_coverage (past : Stages model) (controls delay : Nat)
    (checked : check model start vocabulary encoding law past controls delay = true) :
    ∃ source, produce model start vocabulary encoding law past controls delay = .covered source := by
  unfold produce
  rw [dif_pos checked]
  exact ⟨_,rfl⟩

theorem every_actual_source_case_fits_the_generated_window_count (past : Stages model) (controls : Nat)
    (branch : Stages model) (inside : branch ∈ Cases model past controls) :
    SourceClockTermination.blocks model start branch ≤ blocks model start past controls := by
  have maximum (values : List (Stages model)) : ∀ branch ∈ values,
      SourceClockTermination.blocks model start branch ≤ values.foldr
        (fun entry found => max (SourceClockTermination.blocks model start entry) found) 0 := by
    induction values with
    | nil => intro branch missing; cases missing
    | cons head tail ih =>
      intro branch present
      rcases List.mem_cons.mp present with same | later
      · subst branch; exact le_max_left _ _
      · exact (ih _ later).trans (le_max_right _ _)
  exact maximum _ branch inside

theorem the_source_check_generates_the_actual_window_availability
    (past : Stages model) (controls : Nat)
    (checked : windowsCheck model start vocabulary encoding law past controls = true)
    (branch : Stages model) (inside : branch ∈ Cases model past controls) :
    ServiceActorWindow.Available model start vocabulary encoding law (SourceClockTermination.blocks model start branch) branch := by
  intro block within unfinished
  have capacity := every_actual_source_case_fits_the_generated_window_count model start past controls branch inside
  have endSame : block * width model start + width model start = (block+1) * width model start := by rw [Nat.add_mul,Nat.one_mul]
  have active : branch ∈ ControlServiceEnvelope.cases model start vocabulary encoding law past controls
      (block * width model start) (width model start) true := by
    apply List.mem_filter.mpr
    exact ⟨inside,by simpa only [Bool.not_true,Bool.false_or,decide_eq_true_eq,endSame] using unfinished⟩
  have scanned := List.all_eq_true.mp checked block (List.mem_range.mpr (by omega))
  have nonempty := List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem active)
  simp only [nonempty,Bool.false_eq_true,if_false] at scanned
  refine ⟨ControlServiceEnvelope.Budget.a_checked_source_budget_generates_each_actual_surplus
    model start vocabulary encoding law _ _ _ scanned branch active,?_⟩
  intro offset bounded currentOpen
  exact ControlServiceEnvelope.Budget.a_checked_source_domain_generates_each_actual_communication_gate
    model start vocabulary encoding law _ _ _ scanned branch active offset bounded currentOpen

theorem source_coverage_generates_completion_for_every_adaptive_control
    (past : Stages model) (controls delay : Nat)
    (source : Covered model start vocabulary encoding law past controls delay)
    (choose : Nat → DeliveryControlTree.Stages model.source.code → DeliveryControlTree.Command model.source.code)
    (index : Nat) :
    let actual := DeliveryControlTree.run choose controls index past
    (UnifiedRecoveryRun.produce model start vocabulary encoding law actual).status = .jointComplete ∧
    (UnifiedRecoveryRun.produce model start vocabulary encoding law actual).stages.length ≤
      actual.length + SourceClockTermination.deadline model start actual * CommunicationWorkBudget.slotAllowance model start := by
  dsimp only
  have inside := DeliveryControlTree.every_adaptive_source_choice_is_in_the_generated_tree choose controls index past
  have guard := Bool.and_eq_true_iff.mp source.checked
  have reserve := Bool.and_eq_true_iff.mp guard.2
  have history := Bool.and_eq_true_iff.mp reserve.2
  exact ServiceActorWindow.source_generated_identity_availability_forces_the_original_joint_completion
    model start vocabulary encoding law _ delay (of_decide_eq_true guard.1)
    (of_decide_eq_true (List.all_eq_true.mp reserve.1 _ inside))
    (the_source_check_generates_the_actual_window_availability model start vocabulary encoding law past controls history.2 _ inside)
    ((AdaptiveRejectionHistory.check_iff start delay _).mp (List.all_eq_true.mp history.1 _ inside))

theorem the_same_actual_source_consumes_native_rows_history_receipts_whole_ledger_and_next
    (past : Stages model) (controls delay : Nat)
    (source : Covered model start vocabulary encoding law past controls delay)
    (choose : Nat → DeliveryControlTree.Stages model.source.code → DeliveryControlTree.Command model.source.code)
    (index : Nat) :
    let full := (UnifiedRecoveryRun.produce model start vocabulary encoding law (DeliveryControlTree.run choose controls index past)).stages
    let final := EventHistory.execute start full
    let runtime := WithdrawalInquiryRuntime.runtime model final
    JointResponse.Clear model start vocabulary encoding law full ∧
    (∀ row ∈ (WithdrawalInquiryRuntime.authority model final).current.challenges,
      row.2.isPending (WithdrawalInquiryRuntime.family model final) (WithdrawalInquiryRuntime.sourceIndex model final) = false) ∧
    (DeliveryControlTree.run choose controls index past) <+: full ∧
    StageAccountability.ledger start vocabulary encoding law (DeliveryControlTree.run choose controls index past) <+: StageAccountability.ledger start vocabulary encoding law full ∧
    (∀ receiver, (StageReception.run vocabulary encoding law start (DeliveryControlTree.run choose controls index past) receiver (DeliveryControlTree.run choose controls index past).length).receipts <+:
      (StageReception.run vocabulary encoding law start full receiver full.length).receipts) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  have inside := DeliveryControlTree.every_adaptive_source_choice_is_in_the_generated_tree choose controls index past
  have guard := Bool.and_eq_true_iff.mp source.checked
  have reserve := Bool.and_eq_true_iff.mp guard.2
  have history := Bool.and_eq_true_iff.mp reserve.2
  exact ServiceActorConsumer.the_generated_identity_window_is_consumed_by_the_original_root
    model start vocabulary encoding law _ delay (of_decide_eq_true guard.1)
    (of_decide_eq_true (List.all_eq_true.mp reserve.1 _ inside))
    (the_source_check_generates_the_actual_window_availability model start vocabulary encoding law past controls history.2 _ inside)
    ((AdaptiveRejectionHistory.check_iff start delay _).mp (List.all_eq_true.mp history.1 _ inside))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlServiceConsumer
