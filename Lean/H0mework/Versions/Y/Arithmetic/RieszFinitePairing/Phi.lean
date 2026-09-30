import H0mework.Versions.Y.Arithmetic.RieszFinitePairing.Positive
import H0mework.Versions.Y.Arithmetic.RieszFinitePairing.Negative
import H0mework.Versions.Y.Arithmetic.RieszFinitePairing.SelfPair

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace
open OriginalRieszFiniteSource OriginalRieszFiniteColumns OriginalRieszFiniteSynthesis
noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "K" => burnolCompletedMellinRieszVector

private theorem band_pair_integrable (f : ℝ → ℂ)
    (continuous : ∀ {x : ℝ}, 0 < x → ContinuousAt f x) (shift : ℝ) :
    IntervalIntegrable (fun x : ℝ => star (f x) * f (Real.exp shift * x))
      volume (q * Real.exp (-shift)) q := by
  apply ContinuousOn.intervalIntegrable
  intro x inside
  have minimum : 0 < min (q * Real.exp (-shift)) q := by
    apply lt_min
    · positivity
    · norm_num
  have positive := minimum.trans_le inside.1
  exact ((continuous positive).star.mul
    ((continuous (mul_pos (Real.exp_pos shift) positive)).comp
      (by fun_prop : ContinuousAt (fun y : ℝ => Real.exp shift * y) x))).continuousWithinAt

theorem annularRead_pair (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    annularRead coordinate shift + annularRead coordinate (-shift) =
      -sourcePairRead coordinate shift := by
  rw [annularRead_nonnegative coordinate shift nonnegative,
    annularRead_negative coordinate shift nonnegative]
  unfold sourcePairRead sourceProduct
  rw [intervalIntegral.integral_add
    (band_pair_integrable _ (positionSource_continuousAt coordinate) shift)
    (band_pair_integrable _ (fun positive =>
      burnolRieszSingleFourierSourceRaw_continuousAt coordinate positive.ne') shift)]
  ring

/-- The entire finite forcing, with both physical faces, is computed by the actual source band. -/
theorem forcing_pair_source (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    inner ℂ (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift))
      (K coordinate : BurnolL2) = -sourcePairRead coordinate shift := by
  rw [inner_add_left, forcing_annularRead, forcing_annularRead]
  exact annularRead_pair coordinate shift nonnegative

theorem wholeSourceRead_pair_source (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : |shift| ≤ Real.log 2) :
    wholeSourceRead coordinate shift (K coordinate) +
      wholeSourceRead coordinate (-shift) (K coordinate) = -sourcePairRead coordinate shift := by
  rw [wholeSourceRead_annular coordinate shift bounded,
    wholeSourceRead_annular coordinate (-shift) (by simpa only [abs_neg] using bounded)]
  exact annularRead_pair coordinate shift nonnegative

theorem source_pair_defect (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (bounded : |shift| ≤ Real.log 2) :
    firstSourceRead coordinate shift (K coordinate) +
      firstSourceRead coordinate (-shift) (K coordinate) +
      inner ℂ (burnolAnnulusSamplingL2 (fourierColumn coordinate shift) 0 +
        burnolAnnulusSamplingL2 (fourierColumn coordinate (-shift)) 0)
        (sourceFourierDefect (K coordinate)) = -sourcePairRead coordinate shift := by
  have source := wholeSourceRead_pair_source coordinate shift nonnegative bounded
  simp only [wholeSourceRead_keeps_defect] at source
  simp only [inner_add_left]
  linear_combination source

def evaluatorSource (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : ℂ :=
  (pairedMellinTranslationCharacter coordinate.value shift -
    pairedMellinTranslationCharacter (star coordinate.value) shift) * kernelSelfSource coordinate +
      (1 / 2 : ℂ) * star (sourcePairRead coordinate shift)

theorem original_evaluator_source (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) (nonnegative : 0 ≤ shift) :
    burnolCompletedMellinEvaluator coordinate
      (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) = evaluatorSource coordinate shift := by
  have paired : inner ℂ (K coordinate : BurnolL2)
      (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift)) =
        -star (sourcePairRead coordinate shift) := by
    calc
      _ = star (inner ℂ (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift))
          (K coordinate : BurnolL2)) := (inner_conj_symm _ _).symm
      _ = _ := by rw [forcing_pair_source coordinate shift nonnegative, star_neg]
  rw [OriginalRieszFiniteSource.original_boundary_read,
    original_kernel_self_source, paired]
  unfold evaluatorSource
  ring

theorem fixed_residual_source (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    -burnolPaFixedShiftResidual coordinate zero =
      evaluatorSource coordinate (Real.log stageZeroSonineQ) := by
  have nonnegative : 0 ≤ Real.log stageZeroSonineQ := by
    apply Real.log_nonneg
    change 1 ≤ Real.sqrt 3
    exact (Real.one_le_sqrt).mpr (by norm_num)
  rw [← fixedShiftBoundaryRead_eq_neg_residual,
    original_evaluator_keeps_sourceDefect coordinate zero (Real.log stageZeroSonineQ) fixedShift_small,
    source_pair_defect coordinate (Real.log stageZeroSonineQ) nonnegative fixedShift_small,
    original_kernel_self_source, star_neg]
  unfold evaluatorSource
  ring

theorem evaluatorSource_zero (coordinate : BurnolCompletedMellinCoordinate) :
    evaluatorSource coordinate 0 = 0 := by
  simp [evaluatorSource, sourcePairRead_zero, pairedMellinTranslationCharacter,
    fullMellinTranslationCharacter, reciprocalMellinTranslationCharacter]

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
