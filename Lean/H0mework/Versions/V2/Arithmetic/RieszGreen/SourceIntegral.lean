import H0mework.Versions.V2.Arithmetic.RieszGreen.SourcePairing
import H0mework.Versions.V2.Arithmetic.RieszGreen.SourceOrigin
import H0mework.Versions.V2.Arithmetic.RieszGreen.SourceDerivative
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource

noncomputable section

local notation "q" => (1 / 4 : ℝ)

def sourceFlux (left right : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (x : ℂ) * star (burnolRieszSingleFourierSourceRaw left x) *
    burnolRieszSingleFourierSourceRaw right x

private theorem sourceFlux_continuousAt (left right : BurnolCompletedMellinCoordinate)
    {x : ℝ} (nonzero : x ≠ 0) : ContinuousAt (sourceFlux left right) x :=
  (Complex.continuous_ofReal.continuousAt.mul
    (burnolRieszSingleFourierSourceRaw_continuousAt left nonzero).star).mul
      (burnolRieszSingleFourierSourceRaw_continuousAt right nonzero)

private theorem sourceFlux_derivative (left right : BurnolCompletedMellinCoordinate)
    {x : ℝ} (nonzero : x ≠ 0)
    (leftDerivative : HasDerivAt (burnolRieszSingleFourierSourceRaw left)
      ((weightedRaw left x - (1 / 2 : ℂ) * burnolRieszSingleFourierSourceRaw left x) / (x : ℂ)) x)
    (rightDerivative : HasDerivAt (burnolRieszSingleFourierSourceRaw right)
      ((weightedRaw right x - (1 / 2 : ℂ) * burnolRieszSingleFourierSourceRaw right x) / (x : ℂ)) x) :
    HasDerivAt (sourceFlux left right) (sourcePairDensity left right x) x := by
  have actual := ((Complex.ofRealCLM.hasDerivAt (x := x)).mul leftDerivative.star).mul rightDerivative
  have complexNonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  convert! actual using 1
  simp only [sourcePairDensity, Complex.ofRealCLM_apply, Complex.ofReal_one,
    star_sub, star_mul, star_div₀, star_one, star_ofNat, Complex.star_def, Complex.conj_ofReal,
    Pi.mul_apply]
  field_simp [complexNonzero]
  ring

/-- The two punctured FTC intervals consume the generated origin flux and the original L² density. -/
theorem source_interval_green (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (Euler.sourceEuler left) (burnolRieszSingleFourierSource right) +
      inner ℂ (burnolRieszSingleFourierSource left) (Euler.sourceEuler right) =
      (1 / 2 : ℂ) * star (Kernel.beta left) * Kernel.beta right := by
  have leftDerivative := source_hasDerivAt left
  have rightDerivative := source_hasDerivAt right
  have origin : Tendsto (sourceFlux left right) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    source_cross_origin left right
  have full := sourcePairDensity_intervalIntegrable left right
  have leftIntegral : IntervalIntegrable (sourcePairDensity left right) volume (-q) 0 :=
    full.mono_set (by
      rw [uIcc_of_le (by norm_num : -q ≤ 0), uIcc_of_le (by norm_num : -q ≤ q)]
      exact Icc_subset_Icc le_rfl (by norm_num))
  have rightIntegral : IntervalIntegrable (sourcePairDensity left right) volume 0 q :=
    full.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ q), uIcc_of_le (by norm_num : -q ≤ q)]
      exact Icc_subset_Icc (by norm_num) le_rfl)
  have negativeFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : -q < (0 : ℝ))
    (fun x hx => sourceFlux_derivative left right (by linarith [hx.2])
      (leftDerivative x (by linarith [hx.2])) (rightDerivative x (by linarith [hx.2])))
    leftIntegral
    ((sourceFlux_continuousAt left right (by norm_num : -q ≠ 0)).tendsto.mono_left nhdsWithin_le_nhds)
    (origin.mono_left nhdsWithin_le_nhds)
  have positiveFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0 : ℝ) < q)
    (fun x hx => sourceFlux_derivative left right (by linarith [hx.1])
      (leftDerivative x (by linarith [hx.1])) (rightDerivative x (by linarith [hx.1])))
    rightIntegral (origin.mono_left nhdsWithin_le_nhds)
    ((sourceFlux_continuousAt left right (by norm_num : q ≠ 0)).tendsto.mono_left nhdsWithin_le_nhds)
  rw [← sourcePairDensity_integral,
    ← intervalIntegral.integral_add_adjacent_intervals leftIntegral rightIntegral,
    negativeFTC, positiveFTC]
  unfold sourceFlux Kernel.beta
  rw [burnolRieszSingleFourierSourceRaw_endpoints left,
    burnolRieszSingleFourierSourceRaw_endpoints right]
  push_cast
  ring

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
