import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueuedWindowProgress

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedFundedEntry
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
abbrev rank := CommunicationProgressSource.rank model start vocabulary encoding law
def width := max (ForwardResponseClock.width model start) (QueuedWindowProgress.width model start)
def blocks (past : JointResponse.Stages model) := rank model start vocabulary encoding law past + 1
def deadline (past : JointResponse.Stages model) := blocks model start vocabulary encoding law past * width model start

-- A queue may still contain actual packets. Unconfirmed content remains a separate gate.
def check (count : Nat) (past : JointResponse.Stages model) : Bool :=
  (List.range count).all fun n =>
    let here := atCut model start vocabulary encoding law past (n * width model start)
    decide (UnifiedResponse.duties model start vocabulary encoding law here = []) &&
      FundedSignatureDescent.resources model start vocabulary encoding law (width model start) here

theorem primitive_mixed_window_generates_a_clear_cut_or_strict_progress
    (delay : Nat) (past : JointResponse.Stages model)
    (pending : ¬ CommunicationProgressSource.Clear model start vocabulary encoding law past)
    (noDuties : UnifiedResponse.duties model start vocabulary encoding law past = [])
    (funded : FundedSignatureDescent.resources model start vocabulary encoding law (width model start) past = true)
    (reserve : width model start * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay (atCut model start vocabulary encoding law past (width model start))) :
    CommunicationProgressSource.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past (width model start)) ∨
      rank model start vocabulary encoding law (atCut model start vocabulary encoding law past (width model start)) < rank model start vocabulary encoding law past := by
  cases queue : JointResponse.queueClear model start past with
  | false =>
    have queueFits : QueuedWindowProgress.width model start ≤ width model start := Nat.le_max_right _ _
    have orderedCut := FundedSignatureEntry.actual_cut_is_a_prefix_of_every_later_cut model start vocabulary encoding law past _ _ queueFits
    have localCompliance := FundedSignatureEntry.original_compliance_restricts_to_the_same_prefix model start _ _ orderedCut delay compliant
    have budget := Nat.mul_le_mul_right (CommunicationWorkBudget.slotAllowance model start) queueFits
    have dropped := QueuedWindowProgress.source_queue_turns_force_progress_in_the_actual_mixed_run
      model start vocabulary encoding law past delay queue (by omega) localCompliance
    have later := CommunicationProgressSource.actual_extension_cannot_refill_the_communication_rank model start vocabulary encoding law _ _ orderedCut
    exact Or.inr (lt_of_le_of_lt later dropped)
  | true =>
    have signaturePending : ¬ SignatureEligibility.Clear model start vocabulary encoding law past := by
      intro signatures
      exact pending ⟨⟨signatures.1, signatures.2, noDuties⟩, queue⟩
    cases status : (UnifiedRecoveryRun.run model start vocabulary encoding law (width model start) past).status with
    | jointComplete =>
      have complete := UnifiedRecoveryRun.completion_contains_all_original_joint_gates model start vocabulary encoding law _ past status
      exact Or.inl ⟨complete.1, complete.2.2⟩
    | exhausted =>
      have live := UnifiedRunCost.a_source_reserve_keeps_every_actual_prefix_live model start vocabulary encoding law _ past reserve
      have empty := UnifiedRecoveryRun.exhausted_runs_have_zero_actual_fuel model start vocabulary encoding law _ past status
      omega
    | observationCut =>
      have full := UnifiedRunPrefix.observation_cut_has_all_its_actual_invocations model start vocabulary encoding law _ past status
      have physical := FundedSignatureDescent.actual_invocations_have_at_least_their_trace_length_in_physical_stages
        model start vocabulary encoding law (width model start) past
      rw [full] at physical
      have signatureFits : FundedSignatureDescent.width model start ≤ width model start := Nat.le_max_left _ _
      exact Or.inr (FundedSignatureDescent.actual_funded_signature_work_strictly_spends_the_original_rank
        model start vocabulary encoding law (width model start) delay past (by omega) signaturePending funded compliant)

theorem funded_mixed_channels_generate_a_common_communication_cut
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
      change (decide (UnifiedResponse.duties model start vocabulary encoding law here = []) &&
        FundedSignatureDescent.resources model start vocabulary encoding law (width model start) here) = true at conditions
      have gates := Bool.and_eq_true_iff.mp conditions
      have noData := of_decide_eq_true gates.1
      have endBound : (n + 1) * width model start ≤ deadline model start vocabulary encoding law past :=
        Nat.mul_le_mul_right _ inside
      have endReserve := Nat.mul_le_mul_right (CommunicationWorkBudget.slotAllowance model start) endBound
      have localReserve := FundedSignatureEntry.the_same_source_pays_the_remaining_window_after_its_actual_prefix model start vocabulary encoding law
        past (n * width model start) (width model start) (by
          have aligned : n * width model start + width model start = (n + 1) * width model start := by
            simp only [Nat.add_mul, Nat.one_mul]
          rw [aligned]
          omega)
      have same : atCut model start vocabulary encoding law past ((n + 1) * width model start) =
          atCut model start vocabulary encoding law here (width model start) := by
        rw [Nat.add_mul, Nat.one_mul]
        exact UnifiedRunPrefix.actual_run_prefixes_compose model start vocabulary encoding law _ _ past
      have localCompliant := FundedSignatureEntry.original_compliance_restricts_to_the_same_prefix model start _ _
        (FundedSignatureEntry.actual_cut_is_a_prefix_of_every_later_cut model start vocabulary encoding law past _ _ endBound) delay compliant
      change AdaptiveRejectionHistory.Compliant start delay (atCut model start vocabulary encoding law past ((n + 1) * width model start)) at localCompliant
      rw [same] at localCompliant
      have progress := primitive_mixed_window_generates_a_clear_cut_or_strict_progress
        model start vocabulary encoding law delay here (uncleared n (by omega)) noData gates.2 localReserve localCompliant
      rcases progress with clear | drops
      · rw [← same] at clear
        exact False.elim (uncleared (n + 1) inside clear)
      · change rank model start vocabulary encoding law (atCut model start vocabulary encoding law here (width model start)) <
          rank model start vocabulary encoding law here at drops
        rw [← same] at drops
        change rank model start vocabulary encoding law (atCut model start vocabulary encoding law past ((n + 1) * width model start)) <
          rank model start vocabulary encoding law (atCut model start vocabulary encoding law past (n * width model start)) at drops
        omega
  have impossible := descent (blocks model start vocabulary encoding law past) (Nat.le_refl _)
  unfold blocks at impossible
  omega

theorem primitive_mixed_resources_generate_the_original_communication_entry
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
  obtain ⟨n, inside, cleared⟩ := funded_mixed_channels_generate_a_common_communication_cut
    model start vocabulary encoding law past delay funded reserve compliant
  have blocksBound := Nat.mul_le_mul_right (width model start) inside
  have widthBound : width model start ≤ CommunicationProgressSource.waitLimit model start law + 1 := by
    unfold width QueuedWindowProgress.width CommunicationProgressSource.waitLimit ForwardResponseClock.width
    omega
  have scaled := Nat.mul_le_mul_left (blocks model start vocabulary encoding law past) widthBound
  have horizonBound : n * width model start ≤ CommunicationProgressSource.horizon model start vocabulary encoding law past := by
    unfold blocks rank at scaled blocksBound
    simp only [Nat.add_mul, Nat.one_mul] at scaled blocksBound
    unfold CommunicationProgressSource.horizon CommunicationProgressSource.height
    omega
  have found := FundedSignatureEntry.every_cleared_actual_prefix_is_found_by_the_original_locator model start vocabulary encoding law
    (CommunicationProgressSource.horizon model start vocabulary encoding law past) (n * width model start) past horizonBound cleared
  cases selected : CommunicationProgressSource.locate model start vocabulary encoding law
      (CommunicationProgressSource.horizon model start vocabulary encoding law past) past with
  | none => rw [selected] at found; cases found
  | some index =>
    exact ⟨index, rfl, CommunicationProgressSource.every_located_cut_is_an_actual_common_communication_cut
      model start vocabulary encoding law _ _ _ selected⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedFundedEntry
