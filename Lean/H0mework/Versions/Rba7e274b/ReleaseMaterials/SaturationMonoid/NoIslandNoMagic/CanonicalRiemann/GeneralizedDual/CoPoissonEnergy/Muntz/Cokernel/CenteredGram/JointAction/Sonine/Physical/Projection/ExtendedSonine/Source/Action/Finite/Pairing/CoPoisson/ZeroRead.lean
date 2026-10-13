import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.Phi
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson

open Classical Complex Filter MeasureTheory Set
open scoped InnerProductSpace
open OriginalRieszFinitePairing OriginalRieszFiniteColumns OriginalRieszFiniteSynthesis OriginalPaPhysicalGreen
noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "K" => burnolCompletedMellinRieszVector

private theorem pa_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (value : BurnolL2)
    (member : value ∈ burnolOriginalPaInL2) : inner ℂ value (K coordinate : BurnolL2) = 0 := by
  obtain ⟨physical, inPa, actual⟩ := Submodule.mem_map.mp member
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate zero
  have read := (burnolCompactCoPoissonClosedRange.toSubmodule.mem_orthogonal _).mp
    orthogonal physical inPa
  change inner ℂ (physical : BurnolL2) (K coordinate : BurnolL2) = 0 at read
  change (physical : BurnolL2) = value at actual
  rwa [actual] at read

private theorem pa_fourier (value : BurnolL2) (member : value ∈ burnolOriginalPaInL2) :
    fourierL2 value ∈ burnolOriginalPaInL2 := by
  obtain ⟨physical, inPa, actual⟩ := Submodule.mem_map.mp member
  refine Submodule.mem_map.mpr ⟨evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical,
    burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inPa, ?_⟩
  change fourierL2 (physical : BurnolL2) = fourierL2 value
  exact congrArg fourierL2 actual

private theorem pa_fourier_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (value : BurnolL2)
    (member : value ∈ burnolOriginalPaInL2) :
    inner ℂ value (fourierL2 (K coordinate : BurnolL2)) = 0 := by
  have read := pa_zero coordinate zero (fourierL2 value) (pa_fourier value member)
  have twice : fourierL2 (fourierL2 (K coordinate : BurnolL2)) = (K coordinate : BurnolL2) := by
    rw [fourierL2_fourierL2]
    exact mem_evenL2ClosedFace_iff.mp (K coordinate).property.2
  have pairing := fourierL2.inner_map_map value (fourierL2 (K coordinate : BurnolL2))
  rw [twice] at pairing
  exact pairing.symm.trans read

private theorem exterior_seed_raw (column : BurnolL2) :
    (column - originalPhysicalCutoff q column : BurnolL2) =ᵐ[volume]
      (symmetricInterval q)ᶜ.indicator (column : ℝ → ℂ) := by
  filter_upwards [Lp.coeFn_sub column (originalPhysicalCutoff q column),
    originalPhysicalCutoff_coeFn q column] with x difference cutoff
  rw [difference]
  change column x - originalPhysicalCutoff q column x = _
  rw [cutoff]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_notMem (show x ∉ (symmetricInterval q)ᶜ from not_not_intro inside), sub_self]
  · rw [indicator_of_notMem inside, indicator_of_mem (show x ∈ (symmetricInterval q)ᶜ from inside), sub_zero]

/-- An actual exterior seed reads the original tail together with its full gap mean. -/
theorem exterior_seed_inner (column value : BurnolL2) (raw tail : ℝ → ℂ) (mean : ℂ)
    (regular : Integrable (column : ℝ → ℂ)) (read : (value : ℝ → ℂ) =ᵐ[volume] raw)
    (split : ∀ x : ℝ, raw x = mean + if x ∈ symmetricInterval q then 0 else tail x) :
    inner ℂ (column - originalPhysicalCutoff q column) value =
      mean * star (∫ x : ℝ, (column - originalPhysicalCutoff q column : BurnolL2) x) +
        exteriorRead column tail := by
  let seed : BurnolL2 := column - originalPhysicalCutoff q column
  have seedRaw := exterior_seed_raw column
  have seedRegular : Integrable (seed : ℝ → ℂ) :=
    (regular.indicator (measurableSet_symmetricInterval q).compl).congr seedRaw.symm
  have conjugate : Integrable (fun x : ℝ => star (seed x)) :=
    (@RCLike.conjLIE ℂ _).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp seedRegular
  have exterior := exterior_integrable column value raw tail mean regular read split
  have density : (fun x : ℝ => inner ℂ (seed x) (value x)) =ᵐ[volume]
      fun x => mean * star (seed x) +
        (symmetricInterval q)ᶜ.indicator (fun x => star (column x) * tail x) x := by
    filter_upwards [seedRaw, read] with x source actual
    change seed x = _ at source
    rw [actual, split]
    simp only [RCLike.inner_apply, starRingEnd_apply]
    by_cases inside : x ∈ symmetricInterval q
    · rw [indicator_of_notMem (show x ∉ (symmetricInterval q)ᶜ from not_not_intro inside)] at source
      rw [source, if_pos inside,
        indicator_of_notMem (show x ∉ (symmetricInterval q)ᶜ from not_not_intro inside)]
      simp
    · rw [indicator_of_mem (show x ∈ (symmetricInterval q)ᶜ from inside)] at source
      rw [source, if_neg inside, indicator_of_mem (show x ∈ (symmetricInterval q)ᶜ from inside)]
      ring
  change inner ℂ seed value = _
  rw [L2.inner_def, integral_congr_ae density,
    integral_add (conjugate.const_mul mean)
      ((integrable_indicator_iff (measurableSet_symmetricInterval q).compl).mpr exterior),
    integral_const_mul, integral_indicator (measurableSet_symmetricInterval q).compl]
  simp only [Complex.star_def, integral_conj]
  rfl

/-- The correction keeps every channel and normalization of the actual Pa wave. -/
def positionCorrection (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  positionWave coordinate shift - positionSeed coordinate shift

def fourierCorrection (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  fourierWave coordinate shift - fourierSeed coordinate shift

theorem positionCorrection_realizes (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (test : SchwartzMap ℝ ℂ) :
    (Lp.toTemperedDistributionCLM ℂ volume 2 (positionCorrection coordinate shift)) test =
      burnolRemainderSourceRead (positionSeed coordinate shift) test -
        (Lp.toTemperedDistributionCLM ℂ volume 2 (positionSeed coordinate shift)) test := by
  rw [positionCorrection, map_sub, sub_apply, ← positionSeed_realizes coordinate shift nonnegative test]

theorem fourierCorrection_realizes (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (test : SchwartzMap ℝ ℂ) :
    (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierCorrection coordinate shift)) test =
      burnolRemainderSourceRead (fourierSeed coordinate shift) test -
        (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierSeed coordinate shift)) test := by
  rw [fourierCorrection, map_sub, sub_apply, ← fourierSeed_realizes coordinate shift nonnegative test]

def correctionRead (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : ℂ :=
  inner ℂ (positionCorrection coordinate shift) (K coordinate : BurnolL2) +
    inner ℂ (fourierCorrection coordinate shift) (fourierL2 (K coordinate : BurnolL2)) +
    positionMean coordinate * star (∫ x : ℝ, positionSeed coordinate shift x) +
    fourierMean coordinate * star (∫ x : ℝ, fourierSeed coordinate shift x)

theorem source_programme_zero (coordinate : BurnolCompletedMellinCoordinate) :
    positionSeed coordinate 0 = 0 ∧ fourierSeed coordinate 0 = 0 ∧
      positionWave coordinate 0 = 0 ∧ fourierWave coordinate 0 = 0 ∧
        correctionRead coordinate 0 = 0 := by
  have sources : positionSeed coordinate 0 = 0 ∧ fourierSeed coordinate 0 = 0 ∧
      positionWave coordinate 0 = 0 ∧ fourierWave coordinate 0 = 0 := by
    simp [positionSeed, fourierSeed, positionWave, fourierWave, bandLower,
      burnolWeightedReciprocalStepSource, burnolWeightedReciprocalStepWave,
      burnolReciprocalStepNativeSource, burnolReciprocalStepNativeWave]
  refine ⟨sources.1, sources.2.1, sources.2.2.1, sources.2.2.2, ?_⟩
  simp [correctionRead, positionCorrection, fourierCorrection,
    sources.1, sources.2.1, sources.2.2.1, sources.2.2.2]

theorem positionWave_zero_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    inner ℂ (positionWave coordinate shift) (K coordinate : BurnolL2) = 0 :=
  pa_zero coordinate zero _ (positionWave_inPa coordinate shift nonnegative bounded)

theorem fourierWave_zero_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    inner ℂ (fourierWave coordinate shift) (fourierL2 (K coordinate : BurnolL2)) = 0 :=
  pa_fourier_zero coordinate zero _ (fourierWave_inPa coordinate shift nonnegative bounded)

/-- Original zero annihilation transfers the complete finite band to the actual wave correction and both source masses. -/
theorem sourcePair_correction (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    sourcePairRead coordinate shift = correctionRead coordinate shift := by
  have position := exterior_seed_inner (positionColumn coordinate (-shift)) (K coordinate : BurnolL2)
    _ _ _ (positionColumn_integrable coordinate (-shift))
    (burnolRieszState_ae_raw coordinate) (position_raw coordinate)
  rw [← positionSeed_eq_exterior coordinate shift nonnegative] at position
  have fourier := exterior_seed_inner (fourierColumn coordinate shift) (fourierL2 (K coordinate : BurnolL2))
    _ _ _ (fourierColumn_integrable coordinate shift)
    (burnolRieszFourier_ae_raw coordinate) (fourier_raw coordinate)
  rw [← fourierSeed_eq_exterior coordinate shift nonnegative] at fourier
  have paired := annularRead_pair coordinate shift nonnegative
  simp only [annularRead, positionColumn_integral_zero, fourierColumn_integral_zero,
    star_zero, mul_zero, zero_add] at paired
  rw [exteriorRead_zero_of_quarter _ _ (positionColumn_quarter coordinate shift nonnegative),
    exteriorRead_zero_of_quarter _ _ (fourierColumn_negative_quarter coordinate shift nonnegative)] at paired
  simp only [zero_add, add_zero] at paired
  unfold correctionRead positionCorrection fourierCorrection
  rw [inner_sub_left, inner_sub_left,
    positionWave_zero_read coordinate zero shift nonnegative bounded,
    fourierWave_zero_read coordinate zero shift nonnegative bounded, position, fourier]
  linear_combination paired

/-- The original Tate defect is retained in the same source-correction balance. -/
theorem original_tate_correction (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    firstSourceRead coordinate shift (K coordinate) +
      firstSourceRead coordinate (-shift) (K coordinate) +
      inner ℂ (burnolAnnulusSamplingL2 (fourierColumn coordinate shift) 0 +
        burnolAnnulusSamplingL2 (fourierColumn coordinate (-shift)) 0)
        (sourceFourierDefect (K coordinate)) = -correctionRead coordinate shift := by
  rw [← sourcePair_correction coordinate zero shift nonnegative bounded]
  exact source_pair_defect coordinate shift nonnegative (by rwa [abs_of_nonneg nonnegative])

theorem original_evaluator_correction (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    burnolCompletedMellinEvaluator coordinate
      (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) =
        (pairedMellinTranslationCharacter coordinate.value shift -
          pairedMellinTranslationCharacter (star coordinate.value) shift) * kernelSelfSource coordinate +
            (1 / 2 : ℂ) * star (correctionRead coordinate shift) := by
  rw [original_evaluator_source coordinate zero shift nonnegative, evaluatorSource,
    sourcePair_correction coordinate zero shift nonnegative bounded]

theorem fixed_correction (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    -burnolPaFixedShiftResidual coordinate zero =
      (pairedMellinTranslationCharacter coordinate.value (Real.log stageZeroSonineQ) -
        pairedMellinTranslationCharacter (star coordinate.value) (Real.log stageZeroSonineQ)) *
          kernelSelfSource coordinate +
        (1 / 2 : ℂ) * star (correctionRead coordinate (Real.log stageZeroSonineQ)) := by
  have nonnegative : 0 ≤ Real.log stageZeroSonineQ := by
    apply Real.log_nonneg
    change 1 ≤ Real.sqrt 3
    exact Real.one_le_sqrt.mpr (by norm_num)
  rw [← fixedShiftBoundaryRead_eq_neg_residual,
    original_evaluator_keeps_sourceDefect coordinate zero (Real.log stageZeroSonineQ) fixedShift_small,
    original_tate_correction coordinate zero (Real.log stageZeroSonineQ) nonnegative
      ((le_abs_self _).trans fixedShift_small), original_kernel_self_source, star_neg]
  ring

end
end OriginalRieszFinitePairing.CoPoisson
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
