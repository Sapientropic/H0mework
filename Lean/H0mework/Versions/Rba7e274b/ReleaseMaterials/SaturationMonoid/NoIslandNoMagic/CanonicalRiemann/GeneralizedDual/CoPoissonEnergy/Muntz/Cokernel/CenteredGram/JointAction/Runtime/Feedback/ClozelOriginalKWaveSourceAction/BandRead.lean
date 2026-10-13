import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWaveSourceAction.Coefficient
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalRieszFinitePairing OriginalRieszFiniteColumns OriginalPaPhysicalGreen
local notation "q" => (1 / 4 : ℝ)

private theorem exterior_supported (value : BurnolL2) (radius : ℝ)
    (upper : radius ≤ 4) (supported : originalPhysicalCutoff radius value = value) :
    originalPhysicalCutoff 4 (value - originalPhysicalCutoff q value) =
      value - originalPhysicalCutoff q value := by
  apply cutoff_eq_self_of_ae_zero
  filter_upwards [cutoff_ae_zero radius value supported,
    originalPhysicalCutoff_coeFn q value,
    Lp.coeFn_sub value (originalPhysicalCutoff q value)] with x source cutoff difference
  intro outside
  have absolute : 4 < |x| := lt_of_not_ge (fun member => outside (abs_le.mp member))
  have beyond : x ∉ symmetricInterval radius := fun member =>
    not_lt_of_ge ((abs_le.mpr member).trans upper) absolute
  have beyondQuarter : x ∉ symmetricInterval q := fun member => by
    have small := abs_le.mpr member
    linarith
  rw [difference]
  change value x - originalPhysicalCutoff q value x = 0
  rw [source beyond, cutoff, indicator_of_notMem beyondQuarter, sub_self]

theorem actual_original_seed_complete_support (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    originalPhysicalCutoff 4 (CoPoisson.positionSeed coordinate h) = CoPoisson.positionSeed coordinate h ∧
    originalPhysicalCutoff 4 (CoPoisson.fourierSeed coordinate h) = CoPoisson.fourierSeed coordinate h := by
  have exponential : Real.exp h ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr bounded
  have radius : q * Real.exp h ≤ 4 := by linarith
  have position := positionColumn_cutoff_self coordinate (-h)
  have fourier := fourierColumn_cutoff_self coordinate h
  rw [abs_neg, abs_of_nonneg nonnegative] at position
  rw [abs_of_nonneg nonnegative] at fourier
  rw [CoPoisson.positionSeed_eq_exterior coordinate h nonnegative,
    CoPoisson.fourierSeed_eq_exterior coordinate h nonnegative]
  exact ⟨exterior_supported _ _ radius position, exterior_supported _ _ radius fourier⟩

private theorem actual_tail_tate_pair (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2) :
    burnolMellinTailEvaluator coordinate.value coordinate.rightHalf (burnolTateReciprocalL2 source) =
      inner ℂ (burnolTateReciprocalL2 (burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf)) source := by
  let actualTate : BurnolL2 →ₗᵢ[ℂ] BurnolL2 :=
    { toLinearMap := burnolTateReciprocalL2.toLinearMap
      norm_map' := burnolTateReciprocalValue_norm }
  have paid := actualTate.inner_map_map
    (burnolTateReciprocalL2 (burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf)) source
  change inner ℂ (burnolTateReciprocalL2 (burnolTateReciprocalL2 _))
    (burnolTateReciprocalL2 source) = _ at paid
  rw [burnolTateReciprocalL2_involutive] at paid
  exact paid

/-- The same coefficient reads the actual two finite-band source actors, including their true Tate input. -/
theorem actual_original_coefficient_band_source_read (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    burnolPaResolventSourceCoefficient coordinate
      (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient coordinate h nonnegative bounded) =
      (2 : ℂ) * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h *
        ((∫ x : ℝ, inner ℂ
          ((burnolTateReciprocalL2 (burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf) : BurnolL2) x)
          (CoPoisson.bandRaw h (positionSource coordinate) x)) +
          ∫ x : ℝ, inner ℂ
          ((burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf : BurnolL2) x)
          (CoPoisson.bandRaw h (burnolRieszSingleFourierSourceRaw coordinate) x)) := by
  have support := actual_original_seed_complete_support coordinate h nonnegative bounded
  rw [actual_original_upper_wave_coefficient_action, support.1, support.2, map_add,
    actual_tail_tate_pair]
  change (2 : ℂ) * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h *
    (inner ℂ (burnolTateReciprocalL2 (burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf))
      (CoPoisson.positionSeed coordinate h) +
      inner ℂ (burnolMellinTailKernelL2 coordinate.value coordinate.rightHalf)
        (CoPoisson.fourierSeed coordinate h)) = _
  rw [CoPoisson.positionSeed_pairing coordinate h nonnegative,
    CoPoisson.fourierSeed_pairing coordinate h nonnegative]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
