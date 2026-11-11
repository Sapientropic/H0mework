import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusSourceRealization
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.NextEndpointProgramme

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusProgramme
open Complex MeasureTheory Set Filter BurnolPhysicalState OriginalRieszSource
open scoped Topology InnerProductSpace BigOperators ArithmeticFunction
namespace J
export OriginalWholeDebtRJointMobiusSource (jointValue jointRaw jointMean sourceRaw inverseSource paWave)
end J
local notation "q" => (1 / 4 : ℝ)
local notation "K" => burnolCompletedMellinRieszVector

private theorem joint_gap (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : |x| ≤ q) : J.jointRaw c x = J.jointRaw c 0 := by
  simp only [OriginalWholeDebtRJointMobiusSource.jointRaw, if_pos inside, abs_zero,
    show (0 : ℝ) ≤ q by norm_num, if_true]

private theorem joint_zero (c : BurnolCompletedMellinCoordinate) :
    J.jointRaw c 0 = J.jointMean c := by
  simp [OriginalWholeDebtRJointMobiusSource.jointRaw]



private theorem full_gap (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : |x| ≤ q) : fullSourceRaw c x = 0 :=
  burnolCenteredMobiusInverse_eq_zero_of_quarterGap _ (joint_gap c) inside

theorem actual_source_cut (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    J.sourceRaw c x = (symmetricInterval (4 : ℝ)).indicator (fullSourceRaw c) x := by
  by_cases inside : x ∈ symmetricInterval (4 : ℝ)
  · rw [OriginalWholeDebtRJointMobiusSource.sourceRaw, Set.indicator_of_mem inside, Set.indicator_of_mem inside]
    rw [fullSourceRaw, burnolMobiusFixedWindow_sum _ (joint_gap c) x (abs_le.mpr inside)]
    apply Finset.sum_congr rfl
    intro n _
    simp only [burnolCenteredMobiusSummand, FiniteMobiusResolventFlux.coefficient, joint_zero]
    ring
  · simp only [OriginalWholeDebtRJointMobiusSource.sourceRaw, Set.indicator_of_notMem inside]

private theorem compact_gap (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : |x| ≤ q) : J.sourceRaw c x = 0 := by
  rw [actual_source_cut]
  by_cases window : x ∈ symmetricInterval (4 : ℝ)
  · rw [Set.indicator_of_mem window, full_gap c inside]
  · rw [Set.indicator_of_notMem window]

private theorem outside_gap (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : |x| ≤ q) : outsideSourceRaw c x = 0 := by
  have window : x ∈ symmetricInterval (4 : ℝ) := abs_le.mp (by linarith)
  exact Set.indicator_of_notMem (not_not.mpr window) _

private theorem full_source_split (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    fullSourceRaw c x = J.sourceRaw c x + outsideSourceRaw c x := by
  rw [actual_source_cut]
  unfold outsideSourceRaw
  by_cases window : x ∈ symmetricInterval (4 : ℝ)
  · rw [Set.indicator_of_mem window, Set.indicator_of_notMem (not_not.mpr window), add_zero]
  · rw [Set.indicator_of_notMem window, Set.indicator_of_mem window, zero_add]

private theorem forward_cut (raw : ℝ → ℂ)
    (gap : ∀ {x : ℝ}, |x| ≤ q → raw x = 0) (x : ℝ) :
    burnolInnerGapForward raw x = ∑ n ∈ burnolCenteredMobiusCutoffFinset x,
      (((n : ℕ) : ℂ)⁻¹) * raw (x / (n : ℕ)) := by
  apply tsum_eq_sum
  intro n outside
  have large : burnolCenteredMobiusCutoff x ≤ (n : ℕ) :=
    Nat.le_of_not_gt (by simpa using outside)
  have positive : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  have scaled : |x / (n : ℕ)| ≤ q := by
    rw [abs_div, abs_of_pos positive, div_le_iff₀ positive]
    have cutoffLe : 4 * |x| ≤ ((n : ℕ) : ℝ) :=
      (Nat.le_ceil (4 * |x|)).trans (by exact_mod_cast large)
    nlinarith
  rw [gap scaled, mul_zero]

theorem actual_full_forward_action (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    J.jointRaw c x = burnolInnerGapForward (J.sourceRaw c) x +
      burnolInnerGapForward (outsideSourceRaw c) x + J.jointMean c := by
  have source : burnolInnerGapForward (fullSourceRaw c) x =
      J.jointRaw c x - J.jointMean c := by
    exact (burnolCenteredMobiusInverse_exactReconstruction _ (joint_gap c) x).trans
      (by rw [joint_zero])
  have split : burnolInnerGapForward (fullSourceRaw c) x =
      burnolInnerGapForward (J.sourceRaw c) x +
        burnolInnerGapForward (outsideSourceRaw c) x := by
    rw [forward_cut _ (full_gap c), forward_cut _ (compact_gap c), forward_cut _ (outside_gap c),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [full_source_split, mul_add]
  linear_combination split - source


theorem actual_wave_raw (c : BurnolCompletedMellinCoordinate) :
    (J.paWave c : ℝ → ℂ) =ᵐ[volume]
      fun x => burnolInnerGapForward (J.sourceRaw c) x - sourceMean c := by
  have sourceEq := OriginalWholeDebtRJointMobiusSource.actual_joint_inverse_source c
  have even : reflectL2 (J.inverseSource c) = J.inverseSource c := by
    rw [sourceEq]
    exact burnolMobiusSourceL2_even _
  have gap : (J.inverseSource c : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval q)] fun _ => 0 := by
    rw [sourceEq]
    exact burnolMobiusSourceL2_innerGap _
  have realizes : ∀ test : SchwartzMap ℝ ℂ,
      burnolRemainderSourceRead (J.inverseSource c) test =
        ∫ x : ℝ, test x * (J.paWave c) x := by
    intro test
    simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] using
      OriginalWholeDebtRJointMobiusSource.actual_source_action c test
  obtain ⟨raw, represents, _, wave⟩ :=
    burnolRemainderSourceRead_realization_ae _ _ even gap realizes
  have actual : raw =ᵐ[volume] J.sourceRaw c := represents.symm.trans (OriginalWholeDebtRJointMobiusSource.actual_source_raw c)
  have mean : (∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u) = sourceMean c :=
    integral_congr_ae ((ae_restrict_of_ae actual).mono
      (fun x same => congrArg (fun z : ℂ => (x : ℂ)⁻¹ * z) same))
  filter_upwards [wave, burnolInnerGapForward_ae_congr _ _ actual] with x value forward
  rw [value, forward, mean]

/-- This response is computed from the full outer source and its actual normalization. -/

private theorem outside_response_read (c : BurnolCompletedMellinCoordinate) :
    (((J.jointValue c : BurnolL2) - J.paWave c : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      outsideResponseRaw c := by
  filter_upwards [Lp.coeFn_sub (J.jointValue c : BurnolL2) (J.paWave c),
    OriginalWholeDebtRJointMobiusSource.actual_joint_raw c, actual_wave_raw c] with x difference joint wave
  rw [difference]
  change (J.jointValue c : BurnolL2) x - J.paWave c x = _
  rw [joint, wave, actual_full_forward_action]
  unfold outsideResponseRaw
  ring

private theorem outside_response_memLp (c : BurnolCompletedMellinCoordinate) :
    MemLp (outsideResponseRaw c) 2 volume :=
  (Lp.memLp ((J.jointValue c : BurnolL2) - J.paWave c)).ae_eq (outside_response_read c)

def outsideResponse (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (outside_response_memLp c).toLp (outsideResponseRaw c)

theorem actual_outside_response_raw (c : BurnolCompletedMellinCoordinate) :
    (outsideResponse c : ℝ → ℂ) =ᵐ[volume] outsideResponseRaw c :=
  (outside_response_memLp c).coeFn_toLp

theorem actual_joint_wave_response (c : BurnolCompletedMellinCoordinate) :
    (J.jointValue c : BurnolL2) = J.paWave c + outsideResponse c := by
  have read : (J.jointValue c : BurnolL2) - J.paWave c = outsideResponse c := by
    apply Lp.ext
    exact (outside_response_read c).trans (actual_outside_response_raw c).symm
  exact (sub_eq_iff_eq_add.mp read).trans (add_comm _ _)

theorem actual_K_price (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    inner ℂ (K c : BurnolL2) (J.jointValue c : BurnolL2) =
      inner ℂ (K c : BurnolL2) (outsideResponse c) := by
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c zero
  obtain ⟨physical, physicalPa, physicalRead⟩ :=
    Submodule.mem_map.mp (OriginalWholeDebtRJointMobiusSource.actual_pa_wave c)
  have paid : inner ℂ (K c : BurnolL2) (J.paWave c) = 0 := by
    rw [← physicalRead]
    exact inner_eq_zero_symm.mp (orthogonal physical physicalPa)
  rw [actual_joint_wave_response, inner_add_right, paid, zero_add]

theorem actual_programme_price (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (half : OriginalKCombCalculation.Half observation) :
    let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
    OriginalNextEndpointProgramme.programmePrice c (Real.log stageZeroSonineQ) =
      -inner ℂ (K c : BurnolL2) (outsideResponse c) := by
  dsimp only
  let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
  have fixed := OriginalKCoefficientBFiniteAction.original_fixedResidual_core c
    observation.mathlibZero (Real.log stageZeroSonineQ)
      OriginalKPairedBEulerJunctionSource.junctionShift_pos.le rfl
  rw [OriginalKCoefficientBFiniteAction.sourceKernel_original] at fixed
  calc
    _ = burnolPaFixedShiftResidual c observation.mathlibZero :=
      (OriginalNextEndpointProgramme.original_fixedResidual_programme observation nontrivial half).symm
    _ = -inner ℂ (K c : BurnolL2) (OriginalKCoefficientBFiniteAction.sourceCore c
        (Real.log stageZeroSonineQ)) := fixed
    _ = -inner ℂ (K c : BurnolL2) (J.jointValue c : BurnolL2) :=
      congrArg Neg.neg (OriginalWholeDebtRJointMobiusSource.actual_core_price c).symm
    _ = _ := congrArg Neg.neg (actual_K_price c observation.mathlibZero)

end OriginalWholeDebtRJointMobiusProgramme
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
