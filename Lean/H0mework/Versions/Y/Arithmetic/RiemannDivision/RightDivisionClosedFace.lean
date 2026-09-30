import H0mework.Versions.Y.Arithmetic.RiemannDivision.RightDivisionFubini

/-! # Burnol right-division closed-face landing -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set Filter FourierTransform
open SourceGeneratedComplexFeaturePerfectification
open scoped ENNReal InnerProductSpace

noncomputable section

/-- Production mouth: actual expanding-orbit integrability plus the Fourier
state's own completed-Mellin zero preserve the full physical face.  This
theorem has no `integral_undef` branch. -/
theorem burnolDirectRightResolvent_mem_evenBurnolClosedFace_of_integrable
    (radius : ℝ) (positive : 0 < radius)
    (z : ℂ) (rightQuarter : 1 / 4 < z.re) (belowHalf : z.re < 1 / 2)
    (value : EvenBurnolPhysicalCarrier radius)
    (fourierReadZero :
      burnolRadiusCompletedMellinEvaluator radius positive
        (burnolDivisionCoordinate z rightQuarter belowHalf)
        (evenFaceFourier radius value) = 0)
    (orbitIntegrable : IntegrableOn (fun h : ℝ =>
      positiveMellinQuarterRightResolventWeight z h •
        burnolMultiplicativeDilation (h / 2)
          (fourierL2 (value : BurnolL2)))
      (Ioi (0 : ℝ))) :
    burnolDirectRightResolvent z (value : BurnolL2) ∈
      evenBurnolClosedFace radius := by
  let coordinate := burnolDivisionCoordinate z rightQuarter belowHalf
  let fourierValue : EvenBurnolPhysicalCarrier radius :=
    evenFaceFourier radius value
  have fourierValue_coe : (fourierValue : BurnolL2) =
      fourierL2 (value : BurnolL2) := by rfl
  have directIntegrable : IntegrableOn
      (burnolDirectRightResolventIntegrand z (value : BurnolL2))
      (Ioi (0 : ℝ)) :=
    burnolDirectRightResolventIntegrand_integrableOn_of_fourierExpanding
      z (value : BurnolL2) orbitIntegrable
  have fourierRead := fourierL2_burnolDirectRightResolvent
    z (value : BurnolL2) directIntegrable
  have gapRead :=
    burnolRadiusRestriction_fourierDivisionIntegral_eq_gapConstant
      radius positive coordinate fourierValue fourierReadZero (by
        dsimp only [coordinate]
        simpa only [burnolDivisionCoordinate_half, fourierValue_coe]
          using orbitIntegrable)
  have gapRead' := gapRead
  rw [fourierValue_coe] at gapRead'
  have fourierGap :
      fourierL2 (burnolDirectRightResolvent z (value : BurnolL2)) ∈
        locallyConstantFace radius := by
    rw [mem_locallyConstantFace_iff_exists]
    refine ⟨(2 : ℂ) * burnolConstantGapCoefficient radius fourierValue /
        (1 - coordinate.value), ?_⟩
    rw [fourierRead]
    simpa only [coordinate, fourierValue,
      burnolDivisionCoordinate_half] using gapRead'.symm
  have positionEven := burnolDirectRightResolvent_position_even_of_integrable
    radius positive z value directIntegrable
  exact ⟨⟨positionEven.1, fourierGap⟩, positionEven.2⟩

/-- Feature-completion specialization: source-generated orbit integrability
is consumed internally, so the public mouth contains only physical input
and its Fourier-side completed-Mellin zero. -/
theorem quarterMellinFeatureCompletionEvenAdditive_rightResolvent_mem_evenBurnolClosedFace
    (radius : ℝ) (positive : 0 < radius)
    (z : ℂ) (rightQuarter : 1 / 4 < z.re) (belowHalf : z.re < 1 / 2)
    (value : HilbertAmbient (quarterMellinL2Feature z))
    (physical : quarterMellinFeatureCompletionEvenAdditive z value ∈
      evenBurnolClosedFace radius)
    (fourierReadZero :
      burnolRadiusCompletedMellinEvaluator radius positive
        (burnolDivisionCoordinate z rightQuarter belowHalf)
        (evenFaceFourier radius
          ⟨quarterMellinFeatureCompletionEvenAdditive z value, physical⟩) = 0) :
    quarterMellinFeatureCompletionEvenAdditive z
        (quarterFeatureCompletionRightResolvent z value) ∈
      evenBurnolClosedFace radius := by
  let physicalValue : EvenBurnolPhysicalCarrier radius :=
    ⟨quarterMellinFeatureCompletionEvenAdditive z value, physical⟩
  have orbitIntegrable :=
    fourierExpandingOrbit_integrableOn_of_featureCompletion
      z rightQuarter value
  have directMem :=
    burnolDirectRightResolvent_mem_evenBurnolClosedFace_of_integrable
      radius positive z rightQuarter belowHalf physicalValue fourierReadZero (by
        simpa only [physicalValue] using orbitIntegrable)
  rw [quarterMellinFeatureCompletionEvenAdditive_rightResolvent_eq_direct
    z rightQuarter value]
  exact directMem

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
