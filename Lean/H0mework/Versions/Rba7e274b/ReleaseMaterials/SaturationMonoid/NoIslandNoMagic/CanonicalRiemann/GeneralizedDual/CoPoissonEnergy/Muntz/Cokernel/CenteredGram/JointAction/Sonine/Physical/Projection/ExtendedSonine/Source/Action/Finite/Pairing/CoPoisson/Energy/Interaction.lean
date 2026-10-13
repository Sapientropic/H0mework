import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Energy.FourierGap

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Energy

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalPaPhysicalGreen OriginalRieszFiniteColumns OriginalRieszFiniteSource
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson

noncomputable section
local notation "q" => (1 / 4 : ℝ)

private theorem originalPa_even (value : BurnolL2) (member : value ∈ burnolOriginalPaInL2) :
    reflectL2 value = value := by
  obtain ⟨physical, _, actual⟩ := Submodule.mem_map.mp member
  change (physical : BurnolL2) = value at actual
  rw [← actual]
  exact mem_evenL2ClosedFace_iff.mp physical.property.2

theorem source_wave_forcing_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2)
    (time : ℝ) (timeBound : |time| ≤ Real.log 2) :
    inner ℂ (positionWave coordinate shift + fourierL2 (fourierWave coordinate shift))
        (forcingIntegral coordinate time) =
      inner ℂ (positionSeed coordinate shift) (positionColumn coordinate time) +
        inner ℂ (fourierSeed coordinate shift) (fourierColumn coordinate time) := by
  have position := congrArg (starRingEnd ℂ)
    (positionWave_half_inner coordinate shift nonnegative (positionColumn coordinate time)
      (positionColumn_half coordinate time timeBound) (positionColumn_integral_zero coordinate time))
  simp only [inner_conj_symm] at position
  have fourier := congrArg (starRingEnd ℂ)
    (fourierWave_half_inner coordinate shift nonnegative (fourierColumn coordinate time)
      (fourierColumn_half coordinate time timeBound) (fourierColumn_integral_zero coordinate time))
  simp only [inner_conj_symm] at fourier
  have twice : fourierL2 (fourierL2 (positionWave coordinate shift)) = positionWave coordinate shift := by
    rw [fourierL2_fourierL2, originalPa_even _ (positionWave_inPa coordinate shift nonnegative bounded)]
  have crossPosition : inner ℂ (positionWave coordinate shift) (fourierL2 (fourierColumn coordinate time)) = 0 := by
    have paired := fourierL2.inner_map_map (fourierL2 (positionWave coordinate shift)) (fourierColumn coordinate time)
    rw [twice] at paired
    rw [paired]
    exact inner_eq_zero_symm.mp (positionWave_fourier_half_inner coordinate shift nonnegative bounded
      (fourierColumn coordinate time) (fourierColumn_half coordinate time timeBound)
      (fourierColumn_integral_zero coordinate time))
  have crossFourier : inner ℂ (fourierL2 (fourierWave coordinate shift)) (positionColumn coordinate time) = 0 :=
    inner_eq_zero_symm.mp (fourierWave_fourier_half_inner coordinate shift nonnegative bounded
      (positionColumn coordinate time) (positionColumn_half coordinate time timeBound)
      (positionColumn_integral_zero coordinate time))
  simp only [forcingIntegral_columns, inner_add_left, inner_add_right, fourierL2.inner_map_map,
    position, fourier, crossPosition, crossFourier, add_zero, zero_add]

private theorem exterior_quarter_inner_zero (value test : BurnolL2)
    (supported : originalPhysicalCutoff q test = test) :
    inner ℂ (value - originalPhysicalCutoff q value) test = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_sub value (originalPhysicalCutoff q value),
    originalPhysicalCutoff_coeFn q value, originalPhysicalCutoff_coeFn q test]
    with x difference valueRead testRead
  rw [supported] at testRead
  rw [difference]
  change inner ℂ (value x - originalPhysicalCutoff q value x) (test x) = 0
  rw [valueRead]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, sub_self, inner_zero_left]
  · rw [indicator_of_notMem inside] at testRead
    rw [testRead, inner_zero_right]

private theorem exterior_inner_self (value : BurnolL2) :
    inner ℂ (value - originalPhysicalCutoff q value) value =
      inner ℂ (value - originalPhysicalCutoff q value) (value - originalPhysicalCutoff q value) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub value (originalPhysicalCutoff q value),
    originalPhysicalCutoff_coeFn q value] with x difference cutoff
  simp only [difference, Pi.sub_apply, cutoff]
  by_cases inside : x ∈ symmetricInterval q
  · simp only [indicator_of_mem inside, sub_self, inner_zero_left]
  · simp only [indicator_of_notMem inside, sub_zero]

/-- The actual counted Pa wave consumes both signs of the original finite action as the two native source energies. -/
theorem source_wave_forcing_energy (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    inner ℂ (positionWave coordinate shift + fourierL2 (fourierWave coordinate shift))
        (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift)) =
      inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) +
        inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift) := by
  have positiveBound : |shift| ≤ Real.log 2 := by rwa [abs_of_nonneg nonnegative]
  have negativeBound : |-shift| ≤ Real.log 2 := by simpa only [abs_neg] using positiveBound
  have positionZero : inner ℂ (positionSeed coordinate shift) (positionColumn coordinate shift) = 0 := by
    rw [positionSeed_eq_exterior coordinate shift nonnegative]
    exact exterior_quarter_inner_zero _ _ (positionColumn_quarter coordinate shift nonnegative)
  have fourierZero : inner ℂ (fourierSeed coordinate shift) (fourierColumn coordinate (-shift)) = 0 := by
    rw [fourierSeed_eq_exterior coordinate shift nonnegative]
    exact exterior_quarter_inner_zero _ _ (fourierColumn_negative_quarter coordinate shift nonnegative)
  have positionSelf : inner ℂ (positionSeed coordinate shift) (positionColumn coordinate (-shift)) =
      inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) := by
    simp only [positionSeed_eq_exterior coordinate shift nonnegative]
    exact exterior_inner_self _
  have fourierSelf : inner ℂ (fourierSeed coordinate shift) (fourierColumn coordinate shift) =
      inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift) := by
    simp only [fourierSeed_eq_exterior coordinate shift nonnegative]
    exact exterior_inner_self _
  rw [inner_add_right, source_wave_forcing_pairing coordinate shift nonnegative bounded shift positiveBound,
    source_wave_forcing_pairing coordinate shift nonnegative bounded (-shift) negativeBound,
    positionZero, fourierZero, positionSelf, fourierSelf]
  ring

theorem correction_forcing_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2)
    (time : ℝ) (timeBound : |time| ≤ Real.log 2) :
    inner ℂ (positionCorrection coordinate shift + fourierL2 (fourierCorrection coordinate shift))
        (forcingIntegral coordinate time) =
      -inner ℂ (positionSeed coordinate shift) (fourierL2 (fourierColumn coordinate time)) -
        inner ℂ (fourierL2 (fourierSeed coordinate shift)) (positionColumn coordinate time) := by
  have actual := source_wave_forcing_pairing coordinate shift nonnegative bounded time timeBound
  simp only [forcingIntegral_columns, inner_add_left, inner_add_right, fourierL2.inner_map_map] at actual
  simp only [positionCorrection, fourierCorrection, map_sub, inner_add_left, inner_sub_left,
    forcingIntegral_columns, inner_add_right, fourierL2.inner_map_map]
  linear_combination actual

end
end OriginalRieszFinitePairing.CoPoisson.Energy
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
