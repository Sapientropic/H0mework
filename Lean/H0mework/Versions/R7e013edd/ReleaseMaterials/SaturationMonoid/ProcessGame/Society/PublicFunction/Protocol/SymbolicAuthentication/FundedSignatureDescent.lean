import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationProgressSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FundedSignatureDescent
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

abbrev width := ForwardResponseClock.width model start
abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
abbrev rank := CommunicationProgressSource.rank model start vocabulary encoding law

theorem actual_invocations_have_at_least_their_trace_length_in_physical_stages
    (rounds : Nat) (past : JointResponse.Stages model) :
    past.length + (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).trace.length ≤
      (atCut model start vocabulary encoding law past rounds).length := by
  induction rounds generalizing past with
  | zero =>
    simp only [atCut, UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run]
    split_ifs <;> simp
  | succ rounds ih =>
    cases selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [atCut, UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run, selected, List.length_nil, Nat.add_zero, Nat.le_refl]
    | exhausted empty => simp only [atCut, UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run, selected, List.length_nil, Nat.add_zero, Nat.le_refl]
    | advance action =>
      have positive := CommunicationProgressSource.every_original_dispatch_spends_positive_physical_time model start vocabulary encoding law past action
      have later := ih (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)
      dsimp only [atCut, UnifiedRunPrefix.atCut] at later
      unfold CommunicationProgressSource.cost at positive
      simp only [atCut, UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run, selected, List.length_cons]
      change past.length + ((UnifiedRecoveryRun.run model start vocabulary encoding law rounds _).trace.length + 1) ≤ _
      omega

-- The guard scans original primitive Resources only at actual owned, needed physical cuts.
def resources (rounds : Nat) (past : JointResponse.Stages model) : Bool :=
  decide (SignatureClock.Available model start vocabulary encoding law past
    ((atCut model start vocabulary encoding law past rounds).drop past.length))

theorem actual_funded_signature_work_strictly_spends_the_original_rank
    (rounds delay : Nat) (past : JointResponse.Stages model)
    (room : width model start ≤ (atCut model start vocabulary encoding law past rounds).length - past.length)
    (pending : ¬ SignatureEligibility.Clear model start vocabulary encoding law past)
    (funded : resources model start vocabulary encoding law rounds past = true)
    (compliant : AdaptiveRejectionHistory.Compliant start delay (atCut model start vocabulary encoding law past rounds)) :
    rank model start vocabulary encoding law (atCut model start vocabulary encoding law past rounds) <
      rank model start vocabulary encoding law past := by
  obtain ⟨tail, exactFull⟩ := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law rounds past
  change past ++ tail = atCut model start vocabulary encoding law past rounds at exactFull
  have available : SignatureClock.Available model start vocabulary encoding law past tail := by
    have source := of_decide_eq_true funded
    simpa only [← exactFull, List.drop_left] using source
  have size : width model start ≤ tail.length := by
    rw [← exactFull, List.length_append] at room
    omega
  have opportunity := SignatureWindow.a_pending_signature_forces_an_opportunity_in_the_next_actual_roster_block
    model start vocabulary encoding law past tail size pending available
  have paid := UnifiedServiceWindow.the_same_actual_mixed_history_pays_for_every_signature_opportunity model start vocabulary encoding law rounds past
  have cap := UnifiedServicePotential.actual_compliant_history_has_the_original_capacity model start vocabulary encoding law
    (atCut model start vocabulary encoding law past rounds) delay compliant
  have queue := MixedBirthPotential.actual_extension_cannot_refill_queue_addresses model start past
    (atCut model start vocabulary encoding law past rounds) (by rw [← exactFull]; exact List.prefix_append _ _)
  unfold UnifiedServiceWindow.physical at paid
  change UnifiedServicePotential.used model start vocabulary encoding law past +
    SignatureClock.tally model start vocabulary encoding law past ((atCut model start vocabulary encoding law past rounds).drop past.length) ≤ _ at paid
  rw [← exactFull, List.drop_left] at paid
  change UnifiedServicePotential.used model start vocabulary encoding law past + SignatureClock.tally model start vocabulary encoding law past tail ≤
    UnifiedServicePotential.used model start vocabulary encoding law (atCut model start vocabulary encoding law past rounds) at paid
  unfold rank CommunicationProgressSource.rank UnifiedServicePotential.remaining
  omega

theorem primitive_resources_generate_progress_or_actual_completion_in_one_source_window
    (delay : Nat) (past : JointResponse.Stages model)
    (pending : ¬ SignatureEligibility.Clear model start vocabulary encoding law past)
    (funded : resources model start vocabulary encoding law (width model start) past = true)
    (reserve : width model start * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay (atCut model start vocabulary encoding law past (width model start))) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law (width model start) past).status = .jointComplete ∨
    rank model start vocabulary encoding law (atCut model start vocabulary encoding law past (width model start)) <
      rank model start vocabulary encoding law past := by
  cases status : (UnifiedRecoveryRun.run model start vocabulary encoding law (width model start) past).status with
  | jointComplete => exact Or.inl rfl
  | exhausted =>
    have live := UnifiedRunCost.a_source_reserve_keeps_every_actual_prefix_live model start vocabulary encoding law (width model start) past reserve
    have empty := UnifiedRecoveryRun.exhausted_runs_have_zero_actual_fuel model start vocabulary encoding law (width model start) past status
    omega
  | observationCut =>
    have full := UnifiedRunPrefix.observation_cut_has_all_its_actual_invocations model start vocabulary encoding law (width model start) past status
    have physical := actual_invocations_have_at_least_their_trace_length_in_physical_stages model start vocabulary encoding law (width model start) past
    rw [full] at physical
    exact Or.inr (actual_funded_signature_work_strictly_spends_the_original_rank model start vocabulary encoding law
      (width model start) delay past (by omega) pending funded compliant)

theorem missing_funding_names_the_actual_owned_resource_obstruction
    (rounds : Nat) (past : JointResponse.Stages model)
    (failed : resources model start vocabulary encoding law rounds past = false) :
    ∃ n : Fin ((atCut model start vocabulary encoding law past rounds).drop past.length).length,
      ∃ receiver : Fin model.source.code.sites,
      let here := past ++ ((atCut model start vocabulary encoding law past rounds).drop past.length).take n.val
      Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start here).ownerStart
        (EventStep.seed (EventHistory.execute start here)).history.length = some receiver ∧
      SignatureClock.Needed model start vocabulary encoding law here receiver ∧
      ¬ ResponseEligibility.Resources model start here receiver := by
  have missing := of_decide_eq_false failed
  unfold SignatureClock.Available at missing
  push Not at missing
  exact missing

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FundedSignatureDescent
