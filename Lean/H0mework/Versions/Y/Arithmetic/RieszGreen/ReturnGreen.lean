import H0mework.Versions.Y.Arithmetic.RieszSourceKernel.Generated
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex Filter MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

private theorem interval_inner_read (left right : BurnolQuarterIntervalL2)
    (leftRaw rightRaw : ℝ → ℂ) (leftRead : (left : ℝ → ℂ) =ᵐ[μq] leftRaw)
    (rightRead : (right : ℝ → ℂ) =ᵐ[μq] rightRaw) :
    inner ℂ left right = ∫ x : ℝ in (-q)..q, star (leftRaw x) * rightRaw x := by
  rw [L2.inner_def, intervalIntegral.integral_of_le (by norm_num : -q ≤ q),
    ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [leftRead, rightRead] with x hl hr
  rw [hl, hr]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

private theorem return_raw_green (left right : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in (-q)..q,
      star (Constructor.returnEulerRaw left x) * burnolRieszReturnRaw right x +
        star (burnolRieszReturnRaw left x) * Constructor.returnEulerRaw right x) =
      (1 / 2 : ℂ) * star (burnolRieszReturnRaw left q) * burnolRieszReturnRaw right q := by
  let primitive := fun x : ℝ =>
    (x : ℂ) * star (burnolRieszReturnRaw left x) * burnolRieszReturnRaw right x
  let density := fun x : ℝ =>
    star (Constructor.returnEulerRaw left x) * burnolRieszReturnRaw right x +
      star (burnolRieszReturnRaw left x) * Constructor.returnEulerRaw right x
  have derivative (x : ℝ) : HasDerivAt primitive (density x) x := by
    have actual := ((Complex.ofRealCLM.hasDerivAt (x := x)).mul
      (burnolRieszReturnRaw_hasDerivAt left x).star).mul
        (burnolRieszReturnRaw_hasDerivAt right x)
    convert! actual using 1
    simp only [density, Constructor.returnEulerRaw, Complex.ofRealCLM_apply,
      Complex.ofReal_one, star_add, star_mul, star_div₀, star_one, star_ofNat,
      Complex.star_def, Complex.conj_ofReal, Pi.mul_apply]
    ring
  have firstContinuous : Continuous (fun x : ℝ =>
      star (Constructor.returnEulerRaw left x) * burnolRieszReturnRaw right x) :=
    (Constructor.returnEulerRaw_continuous left).star.mul (burnolRieszReturnRaw_continuous right)
  have secondContinuous : Continuous (fun x : ℝ =>
      star (burnolRieszReturnRaw left x) * Constructor.returnEulerRaw right x) :=
    (burnolRieszReturnRaw_continuous left).star.mul (Constructor.returnEulerRaw_continuous right)
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => derivative x) ((firstContinuous.add secondContinuous).intervalIntegrable (-q) q)
  change (∫ x : ℝ in (-q)..q, density x) = _
  rw [actual]
  dsimp only [primitive]
  have leftEndpoints : burnolRieszReturnRaw left (-q) = burnolRieszReturnRaw left q :=
    burnolRieszSingleFourierReturnRaw_endpoints left
  have rightEndpoints : burnolRieszReturnRaw right (-q) = burnolRieszReturnRaw right q :=
    burnolRieszSingleFourierReturnRaw_endpoints right
  rw [leftEndpoints, rightEndpoints]
  push_cast
  ring

/-- Actual FTC for the smooth return; the original mean-zero projection removes its constant part. -/
theorem return_green (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (Constructor.returnEuler left)
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource right)) +
      inner ℂ (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource left))
        (Constructor.returnEuler right) =
      (1 / 2 : ℂ) * star (burnolRieszReturnRaw left q) * burnolRieszReturnRaw right q := by
  change inner ℂ (Constructor.returnEuler left) (Constructor.returnState right) +
    inner ℂ (Constructor.returnState left) (Constructor.returnEuler right) = _
  unfold Constructor.returnEuler Constructor.zeroMean
  simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  unfold Constructor.returnEulerAmbient
  rw [interval_inner_read _ _ _ _
      (Constructor.compact_read _ (Constructor.returnEulerRaw_continuous left))
      (Constructor.returnState_read right),
    interval_inner_read _ _ _ _ (Constructor.returnState_read left)
      (Constructor.compact_read _ (Constructor.returnEulerRaw_continuous right))]
  rw [← intervalIntegral.integral_add
    (f := fun x : ℝ => star (Constructor.returnEulerRaw left x) * burnolRieszReturnRaw right x)
    (g := fun x : ℝ => star (burnolRieszReturnRaw left x) * Constructor.returnEulerRaw right x)
    (((Constructor.returnEulerRaw_continuous left).star.mul
      (burnolRieszReturnRaw_continuous right)).intervalIntegrable (-q) q)
    (((burnolRieszReturnRaw_continuous left).star.mul
      (Constructor.returnEulerRaw_continuous right)).intervalIntegrable (-q) q)]
  exact return_raw_green left right

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
