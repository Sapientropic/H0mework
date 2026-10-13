import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWaveSourceAction.Source
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

private theorem cutoff_reflection (radius : ℝ) (value : BurnolL2)
    (even : reflectL2 value = value) :
    reflectL2 (originalPhysicalCutoff radius value) = originalPhysicalCutoff radius value := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (originalPhysicalCutoff radius value) negMeasurePreserving,
    originalPhysicalCutoff_coeFn radius value,
    negMeasurePreserving.quasiMeasurePreserving.ae (originalPhysicalCutoff_coeFn radius value),
    Lp.coeFn_compMeasurePreserving value negMeasurePreserving] with x reflected direct opposite source
  change reflectL2 (originalPhysicalCutoff radius value) x = originalPhysicalCutoff radius value (-x) at reflected
  change reflectL2 value x = value (-x) at source
  rw [even] at source
  rw [reflected, direct, opposite]
  have negInside : -x ∈ symmetricInterval radius ↔ x ∈ symmetricInterval radius := by
    change (-radius ≤ -x ∧ -x ≤ radius) ↔ (-radius ≤ x ∧ x ≤ radius)
    constructor <;> intro bounds <;> constructor <;> linarith [bounds.1, bounds.2]
  by_cases inside : x ∈ symmetricInterval radius
  · rw [indicator_of_mem inside, indicator_of_mem (negInside.mpr inside), ← source]
  · rw [indicator_of_notMem inside, indicator_of_notMem (fun member => inside (negInside.mp member))]

private theorem fourier_column_reflection (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    reflectL2 (fourierColumn coordinate h) = fourierColumn coordinate h := by
  have original : reflectL2 (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) =
      burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) := by
    change reflectL2 (burnolRadiusZeroExtension (1 / 4 : ℝ) _) = _
    rw [burnolRadiusZeroExtension_reflect, burnolRieszSingleFourierSource_reflection_fixed]
    rfl
  conv_rhs => rw [fourierColumn_action]
  rw [fourierColumn_action, map_sub, map_smul, reflectL2_burnolMultiplicativeDilation, original]

theorem actual_original_seed_source_reflections (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    reflectL2 (CoPoisson.positionSeed coordinate h) = CoPoisson.positionSeed coordinate h ∧
    reflectL2 (CoPoisson.fourierSeed coordinate h) = CoPoisson.fourierSeed coordinate h := by
  constructor
  · have columnEven : reflectL2 (positionColumn coordinate (-h)) = positionColumn coordinate (-h) := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving (positionColumn coordinate (-h)) negMeasurePreserving,
        negativePositionColumn_even coordinate h] with x reflected direct
      change reflectL2 (positionColumn coordinate (-h)) x = positionColumn coordinate (-h) (-x) at reflected
      exact reflected.trans direct
    rw [CoPoisson.positionSeed_eq_exterior coordinate h nonnegative,
      map_sub, cutoff_reflection _ _ columnEven, columnEven]
  · have columnEven := fourier_column_reflection coordinate h
    rw [CoPoisson.fourierSeed_eq_exterior coordinate h nonnegative,
      map_sub, cutoff_reflection _ _ columnEven, columnEven]

private theorem exterior_gap (value : BurnolL2) :
    ((value - originalPhysicalCutoff (1 / 4) value : BurnolL2) : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub value (originalPhysicalCutoff (1 / 4) value)),
    ae_restrict_of_ae (originalPhysicalCutoff_coeFn (1 / 4) value),
    ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))] with x difference cutoff inside
  rw [difference]
  change value x - originalPhysicalCutoff (1 / 4) value x = 0
  rw [cutoff, indicator_of_mem inside, sub_self]

theorem actual_original_seed_source_gaps (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    (CoPoisson.positionSeed coordinate h : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))] (fun _ => 0) ∧
    (CoPoisson.fourierSeed coordinate h : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))] (fun _ => 0) := by
  rw [CoPoisson.positionSeed_eq_exterior coordinate h nonnegative,
    CoPoisson.fourierSeed_eq_exterior coordinate h nonnegative]
  exact ⟨exterior_gap _, exterior_gap _⟩

def actualPositionWaveAmbient (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) : BurnolPaAmbientCarrier :=
  ⟨CoPoisson.positionWave coordinate h, by
    obtain ⟨physical, _, actual⟩ := Submodule.mem_map.mp
      (CoPoisson.positionWave_inPa coordinate h nonnegative bounded)
    change (physical : BurnolL2) = CoPoisson.positionWave coordinate h at actual
    rw [← actual]
    exact physical.property⟩

def actualFourierWaveAmbient (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) : BurnolPaAmbientCarrier :=
  ⟨CoPoisson.fourierWave coordinate h, by
    obtain ⟨physical, _, actual⟩ := Submodule.mem_map.mp
      (CoPoisson.fourierWave_inPa coordinate h nonnegative bounded)
    change (physical : BurnolL2) = CoPoisson.fourierWave coordinate h at actual
    rw [← actual]
    exact physical.property⟩

theorem actual_original_wave_source_windows (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    burnolMobiusWindowSourceRead (actualPositionWaveAmbient coordinate h nonnegative bounded) =
      burnolRadiusRestriction 4 (CoPoisson.positionSeed coordinate h) ∧
    burnolMobiusWindowSourceRead (actualFourierWaveAmbient coordinate h nonnegative bounded) =
      burnolRadiusRestriction 4 (CoPoisson.fourierSeed coordinate h) := by
  have reflections := actual_original_seed_source_reflections coordinate h nonnegative
  have gaps := actual_original_seed_source_gaps coordinate h nonnegative
  constructor
  · apply burnolRemainderSourceRead_window_source _ _ reflections.1 gaps.1
    intro test
    simpa only [actualPositionWaveAmbient, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_apply, smul_eq_mul] using
      CoPoisson.positionSeed_realizes coordinate h nonnegative test
  · apply burnolRemainderSourceRead_window_source _ _ reflections.2 gaps.2
    intro test
    simpa only [actualFourierWaveAmbient, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_apply, smul_eq_mul] using
      CoPoisson.fourierSeed_realizes coordinate h nonnegative test

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
