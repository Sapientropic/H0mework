import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FundedSignatureDescent

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FundedSignatureEntry
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

abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
abbrev width := ForwardResponseClock.width model start
abbrev rank := CommunicationProgressSource.rank model start vocabulary encoding law
def blocks (past : JointResponse.Stages model) := rank model start vocabulary encoding law past + 1
def deadline (past : JointResponse.Stages model) := blocks model start vocabulary encoding law past * width model start

-- This channel condition concerns data delivery only; unhandled signatures remain admitted.
def dataQuiet (past : JointResponse.Stages model) : Bool :=
  decide (UnifiedResponse.duties model start vocabulary encoding law past = []) && JointResponse.queueClear model start past

def check (count : Nat) (past : JointResponse.Stages model) : Bool :=
  (List.range count).all fun n =>
    let here := atCut model start vocabulary encoding law past (n * width model start)
    dataQuiet model start vocabulary encoding law here &&
      FundedSignatureDescent.resources model start vocabulary encoding law (width model start) here

theorem original_compliance_restricts_to_the_same_prefix
    (first later : JointResponse.Stages model) (ordered : first <+: later) (delay : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start delay later) :
    AdaptiveRejectionHistory.Compliant start delay first := by
  obtain ⟨tail, rfl⟩ := ordered
  intro n inside
  have original := compliant n (by simp only [List.length_append]; omega)
  simpa only [AdaptiveRejectionHistory.rivals, AdaptiveRejectionHistory.slot, List.getElem?_append,
    if_pos inside, List.take_append_of_le_length (Nat.le_of_lt inside)] using original

theorem actual_cut_is_a_prefix_of_every_later_cut
    (past : JointResponse.Stages model) (first later : Nat) (ordered : first ≤ later) :
    atCut model start vocabulary encoding law past first <+: atCut model start vocabulary encoding law past later := by
  have same := UnifiedRunPrefix.actual_run_prefixes_compose model start vocabulary encoding law first (later - first) past
  rw [Nat.add_sub_of_le ordered] at same
  rw [atCut, same]
  exact UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law _ _

theorem the_same_source_pays_the_remaining_window_after_its_actual_prefix
    (past : JointResponse.Stages model) (first later : Nat)
    (reserve : (first + later) * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past) :
    later * CommunicationWorkBudget.slotAllowance model start <
      JointResponse.fuel model start (atCut model start vocabulary encoding law past first) := by
  obtain ⟨tail, same⟩ := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law first past
  have physical := UnifiedRunCost.actual_invocations_pay_all_physical_stages model start vocabulary encoding law first past
  rw [← same, List.length_append] at physical
  have fuel := UnifiedResponse.fuel_after_actual_extension model start past tail
  change JointResponse.fuel model start (past ++ tail) = JointResponse.fuel model start past - tail.length at fuel
  rw [same] at fuel
  rw [Nat.add_mul] at reserve
  change later * CommunicationWorkBudget.slotAllowance model start <
    JointResponse.fuel model start (UnifiedRecoveryRun.run model start vocabulary encoding law first past).stages
  omega

theorem funded_response_channels_generate_a_common_communication_cut
    (past : JointResponse.Stages model) (delay : Nat)
    (funded : check model start vocabulary encoding law (blocks model start vocabulary encoding law past) past = true)
    (reserve : deadline model start vocabulary encoding law past * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay (atCut model start vocabulary encoding law past (deadline model start vocabulary encoding law past))) :
    ∃ n ≤ blocks model start vocabulary encoding law past,
      CommunicationProgressSource.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past (n * width model start)) := by
  have source := List.all_eq_true.mp funded
  by_contra missing
  have uncleared (n : Nat) (inside : n ≤ blocks model start vocabulary encoding law past) :
      ¬ CommunicationProgressSource.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past (n * width model start)) := by
    intro clear
    exact missing ⟨n, inside, clear⟩
  have descent : ∀ n ≤ blocks model start vocabulary encoding law past,
      rank model start vocabulary encoding law (atCut model start vocabulary encoding law past (n * width model start)) + n ≤
        rank model start vocabulary encoding law past := by
    intro n inside
    induction n with
    | zero => simp only [Nat.zero_mul, atCut, UnifiedRunPrefix.zero_has_the_original_stages, Nat.add_zero, Nat.le_refl]
    | succ n ih =>
      have previous := ih (by omega)
      let here := atCut model start vocabulary encoding law past (n * width model start)
      have conditions := source n (List.mem_range.mpr (by omega))
      change (dataQuiet model start vocabulary encoding law here &&
        FundedSignatureDescent.resources model start vocabulary encoding law (width model start) here) = true at conditions
      have gates := Bool.and_eq_true_iff.mp conditions
      have raw := Bool.and_eq_true_iff.mp gates.1
      have noData := of_decide_eq_true raw.1
      have pending : ¬ SignatureEligibility.Clear model start vocabulary encoding law here := by
        intro signatures
        exact uncleared n (by omega) ⟨⟨signatures.1, signatures.2, noData⟩, raw.2⟩
      have endBound : (n + 1) * width model start ≤ deadline model start vocabulary encoding law past :=
        Nat.mul_le_mul_right _ inside
      have endReserve := Nat.mul_le_mul_right (CommunicationWorkBudget.slotAllowance model start) endBound
      have localReserve := the_same_source_pays_the_remaining_window_after_its_actual_prefix model start vocabulary encoding law
        past (n * width model start) (width model start) (by
          have aligned : n * width model start + width model start = (n + 1) * width model start := by
            simp only [Nat.add_mul, Nat.one_mul]
          rw [aligned]
          omega)
      have same : atCut model start vocabulary encoding law past ((n + 1) * width model start) =
          atCut model start vocabulary encoding law here (width model start) := by
        rw [Nat.add_mul, Nat.one_mul]
        exact UnifiedRunPrefix.actual_run_prefixes_compose model start vocabulary encoding law _ _ past
      have localCompliant := original_compliance_restricts_to_the_same_prefix model start _ _
        (actual_cut_is_a_prefix_of_every_later_cut model start vocabulary encoding law past _ _ endBound) delay compliant
      rw [same] at localCompliant
      have progress := FundedSignatureDescent.primitive_resources_generate_progress_or_actual_completion_in_one_source_window
        model start vocabulary encoding law delay here pending gates.2 localReserve localCompliant
      rcases progress with complete | drops
      · have allClear := UnifiedRecoveryRun.completion_contains_all_original_joint_gates model start vocabulary encoding law _ here complete
        have communication : CommunicationProgressSource.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law here (width model start)) :=
          ⟨allClear.1, allClear.2.2⟩
        rw [← same] at communication
        exact False.elim (uncleared (n + 1) inside communication)
      · change rank model start vocabulary encoding law (atCut model start vocabulary encoding law here (width model start)) <
          rank model start vocabulary encoding law here at drops
        rw [← same] at drops
        change rank model start vocabulary encoding law (atCut model start vocabulary encoding law past ((n + 1) * width model start)) <
          rank model start vocabulary encoding law (atCut model start vocabulary encoding law past (n * width model start)) at drops
        omega
  have impossible := descent (blocks model start vocabulary encoding law past) (Nat.le_refl _)
  unfold blocks at impossible
  omega

theorem every_cleared_actual_prefix_is_found_by_the_original_locator
    (rounds index : Nat) (past : JointResponse.Stages model)
    (inside : index ≤ rounds)
    (cleared : CommunicationProgressSource.Clear model start vocabulary encoding law
      (atCut model start vocabulary encoding law past index)) :
    (CommunicationProgressSource.locate model start vocabulary encoding law rounds past).isSome = true := by
  induction rounds generalizing index past with
  | zero =>
    have zero : index = 0 := by omega
    subst index
    rw [atCut, UnifiedRunPrefix.zero_has_the_original_stages] at cleared
    simp only [CommunicationProgressSource.locate, if_pos cleared, Option.isSome_some]
  | succ rounds ih =>
    by_cases initial : CommunicationProgressSource.Clear model start vocabulary encoding law past
    · simp only [CommunicationProgressSource.locate, if_pos initial, Option.isSome_some]
    · cases index with
      | zero =>
        rw [atCut, UnifiedRunPrefix.zero_has_the_original_stages] at cleared
        exact False.elim (initial cleared)
      | succ index =>
        cases selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
        | clear complete => exact False.elim (initial ⟨complete.1, complete.2.2⟩)
        | exhausted empty =>
          simp only [atCut, UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run, selected] at cleared
          exact False.elim (initial cleared)
        | advance action =>
          simp only [atCut, UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run, selected] at cleared
          have found := ih index _ (by omega) cleared
          simpa only [CommunicationProgressSource.locate, if_neg initial, selected, Option.isSome_map] using found

theorem primitive_resources_generate_the_original_communication_entry
    (past : JointResponse.Stages model) (delay : Nat)
    (funded : check model start vocabulary encoding law (blocks model start vocabulary encoding law past) past = true)
    (reserve : deadline model start vocabulary encoding law past * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (atCut model start vocabulary encoding law past (deadline model start vocabulary encoding law past))) :
    ∃ index,
      CommunicationProgressSource.locate model start vocabulary encoding law
        (CommunicationProgressSource.horizon model start vocabulary encoding law past) past = some index ∧
      index ≤ CommunicationProgressSource.horizon model start vocabulary encoding law past ∧
      CommunicationProgressSource.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past index) := by
  obtain ⟨n, inside, cleared⟩ := funded_response_channels_generate_a_common_communication_cut
    model start vocabulary encoding law past delay funded reserve compliant
  have blocksBound := Nat.mul_le_mul_right (width model start) inside
  have widthBound : width model start ≤ CommunicationProgressSource.waitLimit model start law + 1 := by
    unfold CommunicationProgressSource.waitLimit width
    omega
  have scaled := Nat.mul_le_mul_left (blocks model start vocabulary encoding law past) widthBound
  have horizonBound : n * width model start ≤ CommunicationProgressSource.horizon model start vocabulary encoding law past := by
    unfold blocks rank at scaled blocksBound
    simp only [Nat.add_mul, Nat.one_mul] at scaled blocksBound
    unfold CommunicationProgressSource.horizon CommunicationProgressSource.height
    omega
  have found := every_cleared_actual_prefix_is_found_by_the_original_locator model start vocabulary encoding law
    (CommunicationProgressSource.horizon model start vocabulary encoding law past) (n * width model start) past horizonBound cleared
  cases selected : CommunicationProgressSource.locate model start vocabulary encoding law
      (CommunicationProgressSource.horizon model start vocabulary encoding law past) past with
  | none => rw [selected] at found; cases found
  | some index =>
    exact ⟨index, rfl, CommunicationProgressSource.every_located_cut_is_an_actual_common_communication_cut
      model start vocabulary encoding law _ _ _ selected⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FundedSignatureEntry
