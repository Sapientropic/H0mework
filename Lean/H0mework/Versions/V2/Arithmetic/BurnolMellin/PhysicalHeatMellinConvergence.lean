import H0mework.Versions.V2.Arithmetic.BurnolMellin.PhysicalHeatMellinStrip

/-! # Genuine convergence of physical heat-Mellin reads -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set Filter FourierTransform
open scoped ENNReal InnerProductSpace

noncomputable section

/-- The absolute product-kernel estimate already used by generic Gaussian
Fubini also certifies that the displayed heat Mellin transform is an actual
integral, rather than Lean's totalized nonintegrable value. -/
theorem burnolGenericGaussianHeatPair_mellinConvergent
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    MellinConvergent
      (burnolGenericGaussianHeatPairTotal (value : BurnolL2))
      (coordinate.value / 2) := by
  rw [MellinConvergent]
  have joint := burnolGenericGaussianMellinKernel_integrable value coordinate
  have outer := joint.integral_prod_left
  apply (outer.const_mul (2 : ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with scale positiveScale
  rw [burnolGenericGaussianHeatPair_eq_two_mul_positivePair
    value positiveScale]
  simp only [smul_eq_mul]
  change (2 : ℂ) * (∫ x : ℝ in Ioi (0 : ℝ),
      burnolGenericGaussianMellinKernel value coordinate (scale, x)) =
    (scale : ℂ) ^ (coordinate.value / 2 - 1) *
      (2 * burnolGenericGaussianPositivePair (value : BurnolL2) scale)
  rw [show (scale : ℂ) ^ (coordinate.value / 2 - 1) *
      (2 * burnolGenericGaussianPositivePair (value : BurnolL2) scale) =
    2 * ((scale : ℂ) ^ (coordinate.value / 2 - 1) *
      burnolGenericGaussianPositivePair (value : BurnolL2) scale) by ring]
  congr 1
  unfold burnolGenericGaussianPositivePair
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  unfold burnolGenericGaussianMellinKernel burnolGaussianRaw
  ring

/-- Fourier homogeneity transports the preceding genuine convergence to
the complementary center.  This applies to every physical division stage. -/
theorem burnolGenericGaussianHeatPair_complement_mellinConvergent
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    MellinConvergent
      (burnolGenericGaussianHeatPairTotal (value : BurnolL2))
      ((1 - coordinate.value) / 2) := by
  let fourier := evenFaceFourierEquiv burnolUnscaledCommonGapRadius value
  have convergence :=
    burnolGenericGaussianHeatPair_mellinConvergent fourier coordinate
  have heatEq :
      burnolGenericGaussianHeatPairTotal (fourier : BurnolL2) =
        fun scale : ℝ =>
          (scale : ℂ) ^ (-(1 / 2 : ℂ)) *
            burnolGenericGaussianHeatPairTotal
              (value : BurnolL2) scale⁻¹ := by
    funext scale
    exact burnolGenericGaussianHeatPairTotal_fourier value scale
  rw [heatEq] at convergence
  have inverseConvergence : MellinConvergent
      (fun scale : ℝ =>
        burnolGenericGaussianHeatPairTotal (value : BurnolL2) scale⁻¹)
      (coordinate.value / 2 + (-(1 / 2 : ℂ))) :=
    (MellinConvergent.cpow_smul).mp (by
      simpa only [smul_eq_mul] using convergence)
  have transported :=
    (MellinConvergent.comp_rpow
      (f := burnolGenericGaussianHeatPairTotal (value : BurnolL2))
      (s := coordinate.value / 2 + (-(1 / 2 : ℂ)))
      (a := (-1 : ℝ)) (by norm_num)).mp
  have result := transported (by
    simpa only [Real.rpow_neg_one] using inverseConvergence)
  convert result using 1
  norm_num
  ring
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
