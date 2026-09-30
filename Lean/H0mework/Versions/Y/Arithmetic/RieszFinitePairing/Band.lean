import H0mework.Versions.Y.Arithmetic.RieszFinitePairing.ExteriorRaw
import H0mework.Versions.Y.Arithmetic.RieszFinitePairing.Annular

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Complex Filter MeasureTheory Set
open scoped Topology
open OriginalRieszSource

noncomputable section
local notation "q" => (1 / 4 : ℝ)

/-- The original positive gap/tail formula and original return, used only on positive finite bands. -/
def positionSource (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value) - GapEuler.gapMean q coordinate -
    burnolRieszReturnRaw coordinate x

def sourceProduct (coordinate : BurnolCompletedMellinCoordinate) (shift x : ℝ) : ℂ :=
  star (positionSource coordinate x) * positionSource coordinate (Real.exp shift * x) +
    star (burnolRieszSingleFourierSourceRaw coordinate x) *
      burnolRieszSingleFourierSourceRaw coordinate (Real.exp shift * x)

def sourcePairRead (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : ℂ :=
  (2 : ℂ) * (Real.exp (shift / 2) : ℂ) *
    ∫ x : ℝ in (q * Real.exp (-shift))..q, sourceProduct coordinate shift x

theorem positionMean_eq (coordinate : BurnolCompletedMellinCoordinate) :
    positionMean coordinate = GapEuler.gapMean q coordinate -
      burnolQuarterMeanCoefficient (burnolTruncatedFourier
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) := by
  unfold positionMean burnolRieszStateQuarterInnerRaw
  congr 1
  rw [burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)]
  norm_num [GapEuler.gapMean]

theorem positionSource_eq_outer_sub_mean (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    positionSource coordinate x = burnolRieszStatePositiveOuterRaw coordinate x - positionMean coordinate := by
  rw [position_exterior_return_read, positionMean_eq]
  unfold positionSource
  ring

theorem positionTail_positive (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (outside : q < x) : positionTail coordinate x = positionSource coordinate x := by
  have notGap : x ∉ symmetricInterval q := fun inside => not_lt_of_ge inside.2 outside
  have read := position_raw coordinate x
  rw [if_neg notGap, burnolRieszStateRaw_eq_positiveOuter coordinate outside] at read
  rw [positionSource_eq_outer_sub_mean]
  linear_combination -read

theorem positionTail_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    positionTail coordinate (-x) = positionTail coordinate x := by
  unfold positionTail burnolEvenRaw
  simp only [neg_neg]
  ring

theorem fourierTail_eq_source (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    fourierTail coordinate x = burnolRieszSingleFourierSourceRaw coordinate x := by
  unfold fourierTail burnolEvenRaw
  rw [source_raw_even]
  ring

theorem positionSource_continuousAt (coordinate : BurnolCompletedMellinCoordinate)
    {x : ℝ} (positive : 0 < x) : ContinuousAt (positionSource coordinate) x := by
  exact ((continuousAt_const.mul
    (Complex.continuousAt_ofReal_cpow_const x (-star coordinate.value) (Or.inr positive.ne'))).sub
      continuousAt_const).sub (burnolRieszReturnRaw_continuous coordinate).continuousAt

theorem sourceProduct_continuousAt (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) {x : ℝ} (positive : 0 < x) :
    ContinuousAt (sourceProduct coordinate shift) x := by
  have scale : ContinuousAt (fun y : ℝ => Real.exp shift * y) x := by fun_prop
  have moved : 0 < Real.exp shift * x := mul_pos (Real.exp_pos shift) positive
  exact ((positionSource_continuousAt coordinate positive).star.mul
    ((positionSource_continuousAt coordinate moved).comp scale)).add
      ((burnolRieszSingleFourierSourceRaw_continuousAt coordinate positive.ne').star.mul
        ((burnolRieszSingleFourierSourceRaw_continuousAt coordinate moved.ne').comp scale))

theorem sourceProduct_intervalIntegrable (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) :
    IntervalIntegrable (sourceProduct coordinate shift) volume (q * Real.exp (-shift)) q := by
  apply ContinuousOn.intervalIntegrable
  intro x inside
  have minimum : 0 < min (q * Real.exp (-shift)) q := by
    apply lt_min
    · positivity
    · norm_num
  exact (sourceProduct_continuousAt coordinate shift (minimum.trans_le inside.1)).continuousWithinAt

theorem sourcePairRead_zero (coordinate : BurnolCompletedMellinCoordinate) :
    sourcePairRead coordinate 0 = 0 := by
  simp only [sourcePairRead, neg_zero, Real.exp_zero, mul_one, intervalIntegral.integral_same, mul_zero]

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
