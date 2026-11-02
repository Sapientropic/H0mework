import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Padding

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Runtime
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Prefix.Rule model.source.code)
  (past : List (Prefix.Rule model.source.code)) (reference : Program model.source.code (horizon domain))

structure Prepared where
  outcome : Prefix.Outcome model domain original past reference
  compiled : outcome = Prefix.compile model domain original past reference

def prepare : Prepared model domain original past reference := ⟨Prefix.compile model domain original past reference,rfl⟩

variable {model domain original past reference}

abbrev actualHorizon (point : Cursor model.source.code) := Cut.horizon point.source point.entry point.cut
abbrev normalized (point : Cursor model.source.code) (programme : Program model.source.code (horizon domain)) :=
  clip (actualHorizon point) programme
abbrev completeControls (point : Cursor model.source.code) (programme : Program model.source.code (horizon domain)) :=
  Padding.controls original (normalized point programme)
abbrev suffix (point : Cursor model.source.code) (programme : Program model.source.code (horizon domain)) :=
  (completeControls (original := original) point programme).drop past.length
abbrev current (point : Cursor model.source.code) (rival : Opponent model.source.code) := Splice.install point rival past

def realize (point : Cursor model.source.code) (rival : Opponent model.source.code)
    (programme : Program model.source.code (horizon domain)) : Cursor model.source.code :=
  Splice.install (current (past := past) point rival) rival (suffix (original := original) (past := past) point programme)

def Prepared.finish (prepared : Prepared model domain original past reference)
    (point : Replanning.Point model domain) (rival : Opponent model.source.code) : Cursor model.source.code :=
  match prepared.outcome with
  | .selected choice => realize (original := original) (past := past) point.val rival choice.policy.protocol
  | .blocked _ => current (past := past) point.val rival

abbrev Prepared.bound (prepared : Prepared model domain original past reference)
    (point : Replanning.Point model domain) (rival : Opponent model.source.code) :=
  Replanning.native model (prepared.finish point rival)

variable (choice : Prefix.Choice model domain original past reference)
  (point : Replanning.Point model domain) (rival : Opponent model.source.code)

private theorem retained (within : past.length ≤ actualHorizon point.val) :
    (normalized point.val choice.policy.protocol).controls.take past.length = past := by
  have supported := Continuation.Whole.Complete.each_remaining_horizon_is_generated domain point.val point.property
  have old := Prefix.the_selected_plan_really_preserves_the_committed_control_prefix model domain original past reference choice
    (within.trans supported)
  change (choice.policy.protocol.controls.take (actualHorizon point.val)).take past.length = past
  rw [List.take_take,Nat.min_eq_left within]
  exact old

private theorem complete_prefix (within : past.length ≤ actualHorizon point.val) :
    (completeControls (original := original) point.val choice.policy.protocol).take past.length = past :=
  Padding.preserves_prefix original _ past (retained choice point within)

private theorem whole_fold (within : past.length ≤ actualHorizon point.val) :
    realize (original := original) (past := past) point.val rival choice.policy.protocol =
      Splice.install point.val rival (completeControls (original := original) point.val choice.policy.protocol) := by
  have split := List.take_append_drop past.length (completeControls (original := original) point.val choice.policy.protocol)
  rw [complete_prefix choice point within] at split
  change List.foldl _ (List.foldl _ point.val past) _ = _
  rw [←List.foldl_append,split]
  rfl

theorem the_actual_suffix_never_replays_or_changes_its_committed_past
    (ordinal : Nat) (earlier : ordinal ≤ arrival (current (past := past) point.val rival)) :
    Native.Coupling.Match model.source.code (current (past := past) point.val rival).source.input
      (realize (original := original) (past := past) point.val rival choice.policy.protocol).source.input
      (Financial.accountAt (current (past := past) point.val rival).source.input ordinal)
      (Financial.accountAt (realize (original := original) (past := past) point.val rival choice.policy.protocol).source.input ordinal) :=
  Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := model) _ rival _ ordinal earlier

private theorem full_controls_nonempty (positive : 0 < actualHorizon point.val) : completeControls (original := original) point.val choice.policy.protocol ≠ [] := by
  have size : (completeControls (original := original) point.val choice.policy.protocol).length = actualHorizon point.val :=
    Padding.length original (normalized point.val choice.policy.protocol)
  intro empty
  rw [empty] at size
  simp only [List.length_nil] at size
  omega

theorem the_actual_suffix_is_the_same_whole_window_input
    (within : past.length ≤ actualHorizon point.val) (positive : 0 < actualHorizon point.val) :
    (realize (original := original) (past := past) point.val rival choice.policy.protocol).source.input =
      (source point.val original (normalized point.val choice.policy.protocol) rival).input := by
  rw [whole_fold choice point rival within]
  have nonempty := full_controls_nonempty choice point positive
  rw [Splice.input_assembly _ _ original _ nonempty,Padding.same_entire_source]

theorem the_actual_suffix_consumes_exactly_the_remaining_original_window
    (within : past.length ≤ actualHorizon point.val) :
    (realize (original := original) (past := past) point.val rival choice.policy.protocol).cut =
      point.val.cut+actualHorizon point.val := by
  rw [whole_fold choice point rival within]
  change (Installation.Chain.fold point.val rival (completeControls (original := original) point.val choice.policy.protocol)).cut = _
  rw [Installation.Chain.fold_cut (model := model),Padding.length]

theorem the_completed_actual_seed_is_the_verified_whole_seed
    (within : past.length ≤ actualHorizon point.val) (positive : 0 < actualHorizon point.val) :
    seed (realize (original := original) (past := past) point.val rival choice.policy.protocol) =
      seed (Whole.Runtime.execute point.val original (normalized point.val choice.policy.protocol) rival) := by
  have states := Splice.states_assembly point.val rival original
    (completeControls (original := original) point.val choice.policy.protocol) (full_controls_nonempty choice point positive)
  rw [Padding.same_entire_states] at states
  rw [←whole_fold choice point rival within] at states
  change (realize (original := original) (past := past) point.val rival choice.policy.protocol).source.feedbackState
      (realize (original := original) (past := past) point.val rival choice.policy.protocol).entry
      (realize (original := original) (past := past) point.val rival choice.policy.protocol).cut = _
  rw [the_actual_suffix_consumes_exactly_the_remaining_original_window choice point rival within]
  exact congrFun states _

theorem the_actual_completion_is_fully_paid
    (within : past.length ≤ actualHorizon point.val) (positive : 0 < actualHorizon point.val) :
    (seed (realize (original := original) (past := past) point.val rival choice.policy.protocol)).remaining = 0 := by
  rw [the_completed_actual_seed_is_the_verified_whole_seed choice point rival within positive]
  exact Whole.Runtime.the_whole_word_consumes_exactly_its_original_remaining_budget _ _ _ _

theorem normalization_keeps_the_entire_actual_evaluation :
    actualEvaluation model point.val original (normalized point.val choice.policy.protocol) rival =
      actualEvaluation model point.val original choice.policy.protocol rival := by
  apply stages_generate_the_same_complete_evaluation
  intro offset inside
  exact Continuation.Whole.Complete.clipping_keeps_each_consumed_stage _ _ _ _ inside

theorem the_selected_actual_suffix_has_the_original_complete_protection :
    Synthesis.accepts model.source.code (economicAxes point.val.source point.val.cut)
      (actualEvaluation model point.val original (normalized point.val choice.policy.protocol) rival)
      (actualEvaluation model point.val original reference rival) := by
  rw [normalization_keeps_the_entire_actual_evaluation choice point rival]
  exact (Selection.acceptable_iff_every_common_external_opponent model domain original reference choice.policy.protocol).mp
    choice.policy.accepted point rival

abbrev bound := Replanning.native model (realize (original := original) (past := past) point.val rival choice.policy.protocol)
abbrev facade := Native.AuthorityRuntime.facade (bound choice point rival)
abbrev activated := Inquiry.Runtime.readState (bound choice point rival)
  (depth (realize (original := original) (past := past) point.val rival choice.policy.protocol))


theorem the_actual_suffix_preserves_every_raw_word_of_the_verified_whole_plan
    (within : past.length ≤ actualHorizon point.val) (positive : 0 < actualHorizon point.val) (ordinal : Nat) :
    let actual := (realize (original := original) (past := past) point.val rival choice.policy.protocol).source.actualExecution ordinal
    let verified := (source point.val original (normalized point.val choice.policy.protocol) rival).actualExecution ordinal
    actual.before = verified.before ∧ actual.submitted = verified.submitted := by
  have inputs := the_actual_suffix_is_the_same_whole_window_input choice point rival within positive
  constructor <;> (unfold Machine.actualExecution;rw [inputs])

theorem the_actual_root_consumes_the_complete_future_contract_settlement_and_next
    (within : past.length ≤ actualHorizon point.val) (positive : 0 < actualHorizon point.val) :
    let currentRoot := activated choice point rival
    Prefix.Contract model domain original past reference (.selected choice) ∧
      Synthesis.accepts model.source.code (economicAxes point.val.source point.val.cut)
        (actualEvaluation model point.val original (normalized point.val choice.policy.protocol) rival)
        (actualEvaluation model point.val original reference rival) ∧
      (realize (original := original) (past := past) point.val rival choice.policy.protocol).source.input =
        (source point.val original (normalized point.val choice.policy.protocol) rival).input ∧
      (realize (original := original) (past := past) point.val rival choice.policy.protocol).cut =
        point.val.cut+actualHorizon point.val ∧
      (seed (realize (original := original) (past := past) point.val rival choice.policy.protocol)).remaining = 0 ∧
      (∀ ordinal ≤ arrival (current (past := past) point.val rival),
        Native.Coupling.Match model.source.code (current (past := past) point.val rival).source.input
          (realize (original := original) (past := past) point.val rival choice.policy.protocol).source.input
          (Financial.accountAt (current (past := past) point.val rival).source.input ordinal)
          (Financial.accountAt (realize (original := original) (past := past) point.val rival choice.policy.protocol).source.input ordinal)) ∧
      HEq ((facade choice point rival).readoutAt currentRoot .responsibilities)
        (currentRoot.tick.generated.projectionOutcome (.component ())) ∧
      HEq currentRoot.tick.generated.wholeLedgerWriteBack
        (currentRoot.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt currentRoot.current.visit.current) ∧
      currentRoot.tick.nextCurrent = (facade choice point rival).process.stateAt
        ((facade choice point rival).process.successor currentRoot.state) := by
  let currentRoot := activated choice point rival
  have rooted := (facade choice point rival).readoutAt_factorizes currentRoot .responsibilities
  exact ⟨Prefix.every_generated_outcome_has_the_complete_future_contract model domain original past reference (.selected choice),
    the_selected_actual_suffix_has_the_original_complete_protection choice point rival,
    the_actual_suffix_is_the_same_whole_window_input choice point rival within positive,
    the_actual_suffix_consumes_exactly_the_remaining_original_window choice point rival within,
    the_actual_completion_is_fully_paid choice point rival within positive,
    the_actual_suffix_never_replays_or_changes_its_committed_past choice point rival,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩


variable (prepared : Prepared model domain original past reference)

abbrev preparedFacade := Native.AuthorityRuntime.facade (prepared.bound point rival)
abbrev preparedActivated := Inquiry.Runtime.readState (prepared.bound point rival) (depth (prepared.finish point rival))

def ActualProtection : Prefix.Outcome model domain original past reference → Prop
  | .selected selected =>
      Synthesis.accepts model.source.code (economicAxes point.val.source point.val.cut)
        (actualEvaluation model point.val original (normalized point.val selected.policy.protocol) rival)
        (actualEvaluation model point.val original reference rival) ∧
      (past.length ≤ actualHorizon point.val → 0 < actualHorizon point.val →
        (realize (original := original) (past := past) point.val rival selected.policy.protocol).source.input =
          (source point.val original (normalized point.val selected.policy.protocol) rival).input ∧
        (seed (realize (original := original) (past := past) point.val rival selected.policy.protocol)).remaining = 0)
  | .blocked rejected => ∀ tail : Complete.FiniteProgram model.source.code,
      ¬ Selection.holds model domain original reference (Prefix.extension (horizon domain) past tail.2) (rejected tail).row

theorem the_prepared_actual_root_generates_the_complete_contract_settlement_and_next :
    let currentRoot := preparedActivated point rival prepared
    Prefix.Contract model domain original past reference prepared.outcome ∧
      ActualProtection point rival prepared.outcome ∧
      HEq ((preparedFacade point rival prepared).readoutAt currentRoot .responsibilities)
        (currentRoot.tick.generated.projectionOutcome (.component ())) ∧
      HEq currentRoot.tick.generated.wholeLedgerWriteBack
        (currentRoot.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt currentRoot.current.visit.current) ∧
      currentRoot.tick.nextCurrent = (preparedFacade point rival prepared).process.stateAt
        ((preparedFacade point rival prepared).process.successor currentRoot.state) := by
  let currentRoot := preparedActivated point rival prepared
  have rooted := (preparedFacade point rival prepared).readoutAt_factorizes currentRoot .responsibilities
  refine ⟨Prefix.every_generated_outcome_has_the_complete_future_contract _ _ _ _ _ _,?_,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
  cases prepared.outcome with
  | selected selected =>
      exact ⟨the_selected_actual_suffix_has_the_original_complete_protection selected point rival,
        fun within positive => ⟨the_actual_suffix_is_the_same_whole_window_input selected point rival within positive,
          the_actual_completion_is_fully_paid selected point rival within positive⟩⟩
  | blocked rejected => exact fun tail => (rejected tail).broken

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Runtime
