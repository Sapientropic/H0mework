import H0mework.Versions.Y.Arithmetic.RiemannDivision.RightDivisionRepresentative

/-! # Burnol right-division Hilbert--Fubini bridge -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set Filter FourierTransform
open SourceGeneratedComplexFeaturePerfectification
open scoped ENNReal InnerProductSpace

noncomputable section

/-- Radius-generic Hilbert/Fubini bridge to the constant Fourier gap. -/
theorem burnolRadiusRestriction_fourierDivisionIntegral_eq_gapConstant
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate)
    (value : EvenBurnolPhysicalCarrier radius)
    (readZero :
      burnolRadiusCompletedMellinEvaluator radius positive coordinate value = 0)
    (orbitIntegrable : IntegrableOn (fun h : ℝ =>
      positiveMellinQuarterRightResolventWeight (coordinate.value / 2) h •
        burnolMultiplicativeDilation (h / 2) (value : BurnolL2))
      (Ioi (0 : ℝ))) :
    restrictToInterval radius
        (-∫ h : ℝ in Ioi (0 : ℝ),
          positiveMellinQuarterRightResolventWeight
              (coordinate.value / 2) h •
            burnolMultiplicativeDilation (h / 2) (value : BurnolL2)) =
      ((2 : ℂ) * burnolConstantGapCoefficient radius value /
          (1 - coordinate.value)) • intervalConstant radius := by
  let z := coordinate.value / 2
  let intervalMeasure := (volume : Measure ℝ).restrict (symmetricInterval radius)
  let orbit : ℝ → BurnolL2 := fun h =>
    positiveMellinQuarterRightResolventWeight z h •
      burnolMultiplicativeDilation (h / 2) (value : BurnolL2)
  let restrictedOrbit : ℝ → Lp ℂ 2 intervalMeasure := fun h =>
    restrictToInterval radius (orbit h)
  let gapValue : ℂ :=
    (2 : ℂ) * burnolConstantGapCoefficient radius value /
      (1 - coordinate.value)
  have even : reflectL2 (value : BurnolL2) = (value : BurnolL2) :=
    mem_evenL2ClosedFace_iff.mp value.property.2
  have restrictedIntegrable : Integrable restrictedOrbit
      (volume.restrict (Ioi (0 : ℝ))) := by
    change IntegrableOn (fun h : ℝ =>
      restrictToInterval radius (orbit h)) (Ioi (0 : ℝ))
    exact (restrictToInterval radius).integrable_comp orbitIntegrable
  change restrictToInterval radius
      (-∫ h : ℝ in Ioi (0 : ℝ), orbit h) =
    gapValue • intervalConstant radius
  rw [map_neg, ← (restrictToInterval radius).integral_comp_comm orbitIntegrable]
  apply ext_inner_left ℂ
  intro test
  rw [inner_neg_right]
  change -inner ℂ test
      (∫ h : ℝ in Ioi (0 : ℝ), restrictedOrbit h) =
    inner ℂ test (gapValue • intervalConstant radius)
  rw [← integral_inner restrictedIntegrable test]
  have innerOrbitRead :
      (∫ h : ℝ in Ioi (0 : ℝ), inner ℂ test (restrictedOrbit h)) =
        ∫ h : ℝ in Ioi (0 : ℝ), ∫ x : ℝ,
          burnolFourierDivisionPairingKernel radius z
            (value : BurnolL2) test (h, x) ∂intervalMeasure := by
    apply integral_congr_ae
    filter_upwards with h
    rw [L2.inner_def]
    have sectionRead := burnolFourierDivisionPairingKernel_section_ae
      radius z (value : BurnolL2) even test h
    change (fun x : ℝ => burnolFourierDivisionPairingKernel radius z
      (value : BurnolL2) test (h, x)) =ᵐ[intervalMeasure]
        fun x : ℝ => inner ℂ (test x) (restrictedOrbit h x) at sectionRead
    exact integral_congr_ae sectionRead.symm
  rw [innerOrbitRead]
  have joint := burnolFourierDivisionPairingKernel_integrable
    radius coordinate (value : BurnolL2) even test
  rw [← integral_prod _ joint, integral_prod_symm _ joint, ← integral_neg]
  have gapRead := burnolEvenStrongRepresentative_gapConstant_ae
    radius positive coordinate value even readZero
  have testRead := (Lp.aestronglyMeasurable test).ae_eq_mk
  have pointwiseRead : ∀ᵐ x ∂intervalMeasure,
      -(∫ h : ℝ in Ioi (0 : ℝ),
          burnolFourierDivisionPairingKernel radius z
            (value : BurnolL2) test (h, x)) =
        inner ℂ (test x) gapValue := by
    filter_upwards [gapRead, testRead] with x gapAt testAt
    have kernelIntegral :
        (∫ h : ℝ in Ioi (0 : ℝ),
            burnolFourierDivisionPairingKernel radius z
              (value : BurnolL2) test (h, x)) =
          (∫ h : ℝ in Ioi (0 : ℝ),
              Complex.exp (((1 / 2 : ℂ) - z) * (h : ℂ)) *
                burnolEvenStrongRepresentative (value : BurnolL2)
                  (Real.exp (h / 2) * x)) *
            starRingEnd ℂ ((Lp.aestronglyMeasurable test).mk test x) := by
      unfold burnolFourierDivisionPairingKernel
      simp only [RCLike.inner_apply]
      rw [integral_mul_const]
    rw [kernelIntegral, ← testAt, RCLike.inner_apply, ← neg_mul]
    have gapAt' :
        -(∫ h : ℝ in Ioi (0 : ℝ),
            Complex.exp (((1 / 2 : ℂ) - z) * (h : ℂ)) *
              burnolEvenStrongRepresentative (value : BurnolL2)
                (Real.exp (h / 2) * x)) = gapValue := by
      change burnolFourierRightDivisionRaw z
        (burnolEvenStrongRepresentative (value : BurnolL2)) x = gapValue
      exact gapAt
    rw [gapAt']
  rw [integral_congr_ae pointwiseRead, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul gapValue (intervalConstant radius),
    intervalConstant_coeFn radius] with x smulRead constantRead
  change (gapValue • intervalConstant radius : Lp ℂ 2 intervalMeasure) x =
    gapValue * intervalConstant radius x at smulRead
  rw [smulRead, constantRead]
  simp only [mul_one]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
