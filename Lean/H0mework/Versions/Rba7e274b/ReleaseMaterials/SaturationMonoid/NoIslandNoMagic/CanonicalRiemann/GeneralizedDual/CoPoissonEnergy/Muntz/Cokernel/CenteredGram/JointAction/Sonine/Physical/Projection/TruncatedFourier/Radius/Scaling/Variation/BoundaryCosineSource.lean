import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.KernelDerivative

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Pointwise Topology

noncomputable section

local instance burnolBoundaryVariationFiniteMeasure :
    IsFiniteMeasure ((volume : Measure ℝ).restrict (symmetricInterval 1)) where
  measure_univ_lt_top := by
    exact lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top 1)

/-- Burnol's moving endpoint cosine source after recharting `[-r,r]` to `[-1,1]`. -/
def burnolRadiusBoundaryCosineRaw (radius y : ℝ) : ℂ :=
  ((2 * Real.cos (2 * Real.pi * radius ^ 2 * y) : ℝ) : ℂ)

def burnolRadiusBoundaryCosineFirstVariationRaw (radius y : ℝ) : ℂ :=
  ((-8 * Real.pi * radius * y *
    Real.sin (2 * Real.pi * radius ^ 2 * y) : ℝ) : ℂ)

theorem burnolRadiusBoundaryCosineRaw_hasDerivAt
    (radius y : ℝ) :
    HasDerivAt (fun r : ℝ ↦ burnolRadiusBoundaryCosineRaw r y)
      (burnolRadiusBoundaryCosineFirstVariationRaw radius y) radius := by
  have phaseDerivative := ((hasDerivAt_pow 2 radius).const_mul
    (2 * Real.pi)).mul_const y
  have cosineDerivative :=
    (Real.hasDerivAt_cos (2 * Real.pi * radius ^ 2 * y)).comp
      radius phaseDerivative
  have realDerivative := cosineDerivative.const_mul 2
  have source := realDerivative.ofReal_comp
  have source' := source.congr_deriv
    (g' := burnolRadiusBoundaryCosineFirstVariationRaw radius y) (by
      unfold burnolRadiusBoundaryCosineFirstVariationRaw
      push_cast
      ring)
  have functionEq :
      (fun r : ℝ ↦ burnolRadiusBoundaryCosineRaw r y) =ᶠ[𝓝 radius]
        (fun r : ℝ ↦ ((2 *
          (Real.cos ∘ fun t : ℝ ↦ 2 * Real.pi * t ^ 2 * y) r : ℝ) : ℂ)) := by
    filter_upwards with r
    unfold burnolRadiusBoundaryCosineRaw
    simp only [Function.comp_apply]
  have final := source'.congr_of_eventuallyEq functionEq
  simpa only [] using! final

theorem burnolRadiusBoundaryCosineRaw_continuous
    (radius : ℝ) : Continuous (burnolRadiusBoundaryCosineRaw radius) := by
  unfold burnolRadiusBoundaryCosineRaw
  fun_prop

theorem burnolRadiusBoundaryCosineRaw_norm_le_two
    (radius y : ℝ) : ‖burnolRadiusBoundaryCosineRaw radius y‖ ≤ 2 := by
  unfold burnolRadiusBoundaryCosineRaw
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [Real.abs_cos_le_one (2 * Real.pi * radius ^ 2 * y)]

theorem burnolRadiusBoundaryCosineRaw_memLp (radius : ℝ) :
    MemLp (burnolRadiusBoundaryCosineRaw radius) 2
      ((volume : Measure ℝ).restrict (symmetricInterval 1)) :=
  (memLp_top_of_bound
      (burnolRadiusBoundaryCosineRaw_continuous radius).aestronglyMeasurable
      2 (Filter.Eventually.of_forall
        (burnolRadiusBoundaryCosineRaw_norm_le_two radius))).mono_exponent
    (by norm_num)

def burnolRadiusBoundaryCosineState (radius : ℝ) : BurnolUnitIntervalL2 :=
  (burnolRadiusBoundaryCosineRaw_memLp radius).toLp
    (burnolRadiusBoundaryCosineRaw radius)

theorem burnolRadiusBoundaryCosineState_coe (radius : ℝ) :
    (burnolRadiusBoundaryCosineState radius : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ).restrict (symmetricInterval 1)]
      burnolRadiusBoundaryCosineRaw radius :=
  MemLp.coeFn_toLp (burnolRadiusBoundaryCosineRaw_memLp radius)

end


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
