import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionShell
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualLanding
import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Spectral.Direct.ClozelBurnolPaRiemannConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedEvaluator

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalPaPhysicalGreen OriginalRieszFiniteColumns
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "K" => burnolCompletedMellinRieszVector

local instance : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem cutoff_integrable (value : BurnolL2) : Integrable (originalPhysicalCutoff q value : ℝ → ℂ) := by
  have localValue : Integrable (value : ℝ → ℂ) μq := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    ((Lp.memLp value).mono_measure Measure.restrict_le_self)
  exact ((integrable_indicator_iff (measurableSet_symmetricInterval q)).mpr localValue).congr
    (originalPhysicalCutoff_coeFn q value).symm

private theorem dilation_integrable (value : BurnolL2) (integrable : Integrable value) (h : ℝ) :
    Integrable (burnolMultiplicativeDilation h value : BurnolL2) := by
  have raw := ((integrable_comp_mul_left_iff (value : ℝ → ℂ) (Real.exp_ne_zero h)).mpr
    integrable).const_mul (Real.exp (h / 2) : ℂ)
  exact raw.congr (burnolMultiplicativeDilation_coeFn h value).symm

private theorem dilation_integral (value : BurnolL2) (h : ℝ) :
    (∫ x : ℝ, burnolMultiplicativeDilation h value x) =
      (Real.exp (-h / 2) : ℂ) * ∫ x : ℝ, value x := by
  rw [integral_congr_ae (burnolMultiplicativeDilation_coeFn h value)]
  unfold burnolL2RawNormalizedDilation
  rw [integral_const_mul, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr (Real.exp_pos h)),
    Complex.real_smul, Complex.ofReal_inv, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Real.exp_neg, ← Real.exp_add]
  congr 2
  ring

private theorem cutoff_pair (seed value : BurnolL2) (mean : ℂ)
    (gap : (value : ℝ → ℂ) =ᵐ[μq] fun _ => mean) :
    inner ℂ (originalPhysicalCutoff q seed) value = mean * star (∫ x : ℝ, originalPhysicalCutoff q seed x) := by
  rw [L2.inner_def]
  have same := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp gap
  calc
    _ = ∫ x : ℝ, mean * star (originalPhysicalCutoff q seed x) := by
      apply integral_congr_ae
      filter_upwards [originalPhysicalCutoff_coeFn q seed, same] with x cut actual
      simp only [RCLike.inner_apply, starRingEnd_apply]
      by_cases inside : x ∈ symmetricInterval q
      · rw [actual inside]
      · rw [cut, indicator_of_notMem inside, star_zero, mul_zero, mul_zero]
    _ = _ := by simp only [integral_const_mul, star_def, integral_conj]

private theorem shell_correction (seed value : BurnolL2) (mean : ℂ)
    (supported : originalPhysicalCutoff q seed = seed)
    (gap : (value : ℝ → ℂ) =ᵐ[μq] fun _ => mean) (shift : ℝ) :
    -inner ℂ (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) seed) -
      burnolMultiplicativeDilation (-shift) seed) value +
      mean * star (∫ x : ℝ, (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) seed) -
        burnolMultiplicativeDilation (-shift) seed : BurnolL2) x) =
      inner ℂ seed (burnolMultiplicativeDilation shift value) -
        (Real.exp (shift / 2) : ℂ) * inner ℂ seed value := by
  have seedInt : Integrable (seed : ℝ → ℂ) := by rw [← supported]; exact cutoff_integrable seed
  have movedInt := dilation_integrable seed seedInt (-shift)
  have mass : (∫ x : ℝ, (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) seed) -
      burnolMultiplicativeDilation (-shift) seed : BurnolL2) x) =
      (∫ x : ℝ, originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) seed) x) -
      ∫ x : ℝ, burnolMultiplicativeDilation (-shift) seed x := by
    rw [integral_congr_ae (Lp.coeFn_sub _ _)]
    exact integral_sub (cutoff_integrable _) movedInt
  have initial := cutoff_pair seed value mean gap
  rw [supported] at initial
  have moved := (burnolMultiplicativeDilation (-shift)).inner_map_eq_flip seed value
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at moved
  rw [inner_sub_left, cutoff_pair _ value mean gap, mass, star_sub, dilation_integral, neg_neg,
    star_mul, moved, initial]
  have realStar : star (Real.exp (shift / 2) : ℂ) = (Real.exp (shift / 2) : ℂ) := Complex.conj_ofReal _
  rw [realStar]
  ring

private theorem position_gap (coordinate : BurnolCompletedMellinCoordinate) :
    ((K coordinate : BurnolL2) : ℝ → ℂ) =ᵐ[μq] fun _ => positionMean coordinate := by
  filter_upwards [ae_restrict_of_ae (burnolRieszState_ae_raw coordinate), ae_restrict_mem
    (measurableSet_symmetricInterval q)] with x source inside
  rw [source, position_raw, if_pos inside, add_zero]

private theorem fourier_gap (coordinate : BurnolCompletedMellinCoordinate) :
    (fourierL2 (K coordinate : BurnolL2) : ℝ → ℂ) =ᵐ[μq] fun _ => fourierMean coordinate := by
  filter_upwards [ae_restrict_of_ae (burnolRieszFourier_ae_raw coordinate), ae_restrict_mem
    (measurableSet_symmetricInterval q)] with x source inside
  rw [source, fourier_raw, if_pos inside, add_zero]

/-- Both original mean terms are computed inside the same counted-source correlations. -/
theorem source_pair (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    sourcePairRead coordinate shift =
      inner ℂ (PositionCounting.value coordinate zero) (burnolMultiplicativeDilation shift (K coordinate : BurnolL2)) -
        (Real.exp (shift / 2) : ℂ) * inner ℂ (PositionCounting.value coordinate zero) (K coordinate : BurnolL2) +
      inner ℂ (CountingDual.value coordinate) (burnolMultiplicativeDilation shift (fourierL2 (K coordinate : BurnolL2))) -
        (Real.exp (shift / 2) : ℂ) * inner ℂ (CountingDual.value coordinate) (fourierL2 (K coordinate : BurnolL2)) := by
  rw [sourcePair_correction coordinate zero shift nonnegative bounded]
  unfold correctionRead positionCorrection fourierCorrection
  rw [inner_sub_left, inner_sub_left, positionWave_zero_read coordinate zero shift nonnegative bounded,
    fourierWave_zero_read coordinate zero shift nonnegative bounded]
  simp only [zero_sub]
  rw [PositionShell.original_seed coordinate zero shift nonnegative bounded,
    DualShell.limit_fourier_seed coordinate shift nonnegative bounded]
  have position := shell_correction (PositionCounting.value coordinate zero) (K coordinate : BurnolL2)
    (positionMean coordinate) (PositionCounting.value_support coordinate zero) (position_gap coordinate) shift
  have fourier := shell_correction (CountingDual.value coordinate) (fourierL2 (K coordinate : BurnolL2))
    (fourierMean coordinate) (show originalPhysicalCutoff q (CountingDual.value coordinate) = CountingDual.value coordinate from
      (DualLanding.original_support coordinate).symm) (fourier_gap coordinate) shift
  linear_combination position + fourier

/-- This is the literal original evaluator, expressed through the actual two counting outputs. -/
theorem original_evaluator (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    evaluatorSource coordinate shift =
      (pairedMellinTranslationCharacter coordinate.value shift - pairedMellinTranslationCharacter (star coordinate.value) shift) *
        kernelSelfSource coordinate + (1 / 2 : ℂ) * star
      (inner ℂ (PositionCounting.value coordinate zero) (burnolMultiplicativeDilation shift (K coordinate : BurnolL2)) -
        (Real.exp (shift / 2) : ℂ) * inner ℂ (PositionCounting.value coordinate zero) (K coordinate : BurnolL2) +
      inner ℂ (CountingDual.value coordinate) (burnolMultiplicativeDilation shift (fourierL2 (K coordinate : BurnolL2))) -
        (Real.exp (shift / 2) : ℂ) * inner ℂ (CountingDual.value coordinate) (fourierL2 (K coordinate : BurnolL2))) := by
  rw [evaluatorSource, source_pair coordinate zero shift nonnegative bounded]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.CountedEvaluator
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
