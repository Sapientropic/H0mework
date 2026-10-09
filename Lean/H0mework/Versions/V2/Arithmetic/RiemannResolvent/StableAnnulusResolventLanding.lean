import H0mework.Versions.V2.Arithmetic.RiemannResolvent.QuarterFeatureCompletionRightResolvent
import H0mework.Versions.V2.Arithmetic.RiemannAnnulus.CompactCoPoissonQuarterProjection

/-!
# Resolvent landing for any source-generated stable annulus orbit

This module extracts the reusable source contract behind the Burnol
closed-range calculation.  A compact source supplies its own dilated compact
faces on a finite positive segment.  The feature-completion action then
generates the physical boundary landing and the quotient character equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set
open SourceGeneratedComplexFeaturePerfectification
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped ENNReal

noncomputable section

local instance burnolStableOrbitAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- A source-owned positive dilation segment in the fixed compact-annulus
carrier.  The equality field retains the actual Schwartz action. -/
structure BurnolCompactAnnulusDilationSegment
    (source : burnolCompactAnnulusSource) where
  sourceAt : (shift : ℝ) → 0 ≤ shift → shift ≤ Real.log 16 →
    burnolCompactAnnulusSource
  sourceAt_coe : ∀ (shift : ℝ) (nonnegative : 0 ≤ shift)
      (bounded : shift ≤ Real.log 16),
    (sourceAt shift nonnegative bounded).1 =
      quarterMuntzSchwartzDilationAction
        (Real.exp shift) (Real.exp_pos shift) source.1

def burnolSourceQuarterRelation
    (source : burnolCompactAnnulusSource)
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    QuarterMellinL2Test z :=
  coPoissonQuarterMellinConvergentMap z positive belowHalf source.1

def burnolSourceQuarterCompletionValue
    (source : burnolCompactAnnulusSource)
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    HilbertAmbient (quarterMellinL2Feature z) :=
  canonicalHilbertMap (quarterMellinL2Feature z)
    (burnolSourceQuarterRelation source z positive belowHalf)

/-- The physical rechart used for any source in the quarter-feature
completion. -/
def burnolSourceFeatureCompletionPhysicalMap (z : ℂ) :
    HilbertAmbient (quarterMellinL2Feature z) →L[ℂ]
      BurnolPaAmbientCarrier :=
  burnolEvenAmbientProjection.comp
    (quarterMellinFeatureCompletionEvenAdditive z)

/-- Completion boundary written by the finite orbit segment of a source. -/
def burnolSourceQuarterCompletionBoundary
    (source : burnolCompactAnnulusSource)
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (shift : ℝ) : HilbertAmbient (quarterMellinL2Feature z) :=
  ∫ base : ℝ in Ioc (0 : ℝ) shift,
    quarterFeatureCompletionRightResolventIntegrand z
      (burnolSourceQuarterCompletionValue source z positive belowHalf) base

theorem burnolSourceQuarterCompletionBoundary_realization
    (source : burnolCompactAnnulusSource)
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (shift : ℝ) :
    hilbertAmbientRealization (quarterMellinL2Feature z)
        (burnolSourceQuarterCompletionBoundary
          source z positive belowHalf shift) =
      positiveMellinQuarterRightResolventBoundarySource z
        (quarterMellinL2Feature z
          (burnolSourceQuarterRelation source z positive belowHalf)) shift := by
  unfold burnolSourceQuarterCompletionBoundary
    positiveMellinQuarterRightResolventBoundarySource
  rw [← LinearIsometry.integral_comp_comm
    (hilbertAmbientRealization (quarterMellinL2Feature z))]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro base _
  change hilbertAmbientRealization (quarterMellinL2Feature z)
      (quarterFeatureCompletionRightResolventIntegrand z
        (burnolSourceQuarterCompletionValue source z positive belowHalf) base) = _
  rw [quarterFeatureCompletionRightResolventIntegrand_realization]
  unfold burnolSourceQuarterCompletionValue
  rw [hilbertAmbientRealization_source_readback]

theorem burnolSourceFeatureCompletionPhysicalMap_orbit
    (source : burnolCompactAnnulusSource)
    (segment : BurnolCompactAnnulusDilationSegment source)
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (base : ℝ) (baseNonnegative : 0 ≤ base)
    (baseBounded : base ≤ Real.log 16) :
    burnolSourceFeatureCompletionPhysicalMap z
        (quarterFeatureCompletionRightResolventIntegrand z
          (burnolSourceQuarterCompletionValue source z positive belowHalf)
          base) =
      (2 * positiveMellinQuarterRightResolventWeight z base) •
        burnolCompactAdditivePhysicalState
          (segment.sourceAt base baseNonnegative baseBounded) := by
  unfold quarterFeatureCompletionRightResolventIntegrand
    burnolSourceQuarterCompletionValue
    burnolSourceFeatureCompletionPhysicalMap
  rw [map_smul, quarterFeatureCompletionTranslation_source,
    ContinuousLinearMap.comp_apply,
    quarterMellinFeatureCompletionEvenAdditive_source, map_smul]
  have relationSquare := LinearMap.congr_fun
    (quarterDilation_muntzRelation_square z positive belowHalf
      (Real.exp base) (Real.exp_pos base)) source.1
  change quarterDilationTestAction z (Real.exp base) (Real.exp_pos base)
      (burnolSourceQuarterRelation source z positive belowHalf) =
    coPoissonQuarterMellinConvergentMap z positive belowHalf
      (quarterMuntzSchwartzDilationAction
        (Real.exp base) (Real.exp_pos base) source.1) at relationSquare
  rw [relationSquare]
  rw [← segment.sourceAt_coe base baseNonnegative baseBounded]
  change positiveMellinQuarterRightResolventWeight z base •
      ((2 : ℂ) • quarterMellinAdditiveProjectedPhysicalState
        (coPoissonQuarterMellinConvergentMap z positive belowHalf
          (segment.sourceAt base baseNonnegative baseBounded).1)) = _
  rw [compactQuarterMellinAdditiveProjectedPhysicalState_eq]
  simp only [smul_smul]
  congr 1
  ring

def burnolSourceQuarterBoundaryPhysicalLanding
    (source : burnolCompactAnnulusSource)
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (shift : ℝ) : BurnolPaAmbientCarrier :=
  burnolSourceFeatureCompletionPhysicalMap z
    (burnolSourceQuarterCompletionBoundary source z positive belowHalf shift)

/-- The action-generated finite boundary lies in the existing compact
co-Poisson range.  Membership is derived pointwise from the source segment. -/
theorem burnolSourceQuarterBoundaryPhysicalLanding_mem_closedRange
    (source : burnolCompactAnnulusSource)
    (segment : BurnolCompactAnnulusDilationSegment source)
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (shift : ℝ) (shiftBounded : shift ≤ Real.log 16) :
    burnolSourceQuarterBoundaryPhysicalLanding
        source z positive belowHalf shift ∈
      burnolCompactCoPoissonClosedRange := by
  let completionValue := burnolSourceQuarterCompletionValue
    source z positive belowHalf
  let completionPath : ℝ → HilbertAmbient (quarterMellinL2Feature z) :=
    quarterFeatureCompletionRightResolventIntegrand z completionValue
  let physicalMap := burnolSourceFeatureCompletionPhysicalMap z
  let physicalPath : ℝ → BurnolPaAmbientCarrier :=
    fun base => physicalMap (completionPath base)
  have completionContinuous : Continuous completionPath :=
    quarterFeatureCompletionRightResolventIntegrand_continuous z completionValue
  have completionIntegrable : IntegrableOn completionPath (Ioc (0 : ℝ) shift) :=
    (completionContinuous.continuousOn.integrableOn_compact isCompact_Icc
      ).mono_set Ioc_subset_Icc_self
  have physicalContinuous : Continuous physicalPath :=
    physicalMap.continuous.comp completionContinuous
  have physicalIntegrable : IntegrableOn physicalPath (Ioc (0 : ℝ) shift) :=
    (physicalContinuous.continuousOn.integrableOn_compact isCompact_Icc
      ).mono_set Ioc_subset_Icc_self
  let rangeProjection :=
    burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
  apply burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_eq_self_iff.mp
  unfold burnolSourceQuarterBoundaryPhysicalLanding
    burnolSourceQuarterCompletionBoundary
  change rangeProjection (physicalMap
      (∫ base : ℝ in Ioc (0 : ℝ) shift, completionPath base)) =
    physicalMap (∫ base : ℝ in Ioc (0 : ℝ) shift, completionPath base)
  calc
    _ = rangeProjection
        (∫ base : ℝ in Ioc (0 : ℝ) shift, physicalPath base) := by
      rw [physicalMap.integral_comp_comm completionIntegrable]
    _ = ∫ base : ℝ in Ioc (0 : ℝ) shift,
        rangeProjection (physicalPath base) := by
      rw [rangeProjection.integral_comp_comm physicalIntegrable]
    _ = ∫ base : ℝ in Ioc (0 : ℝ) shift, physicalPath base := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro base membership
      have baseNonnegative : 0 ≤ base := membership.1.le
      have baseBounded : base ≤ Real.log 16 :=
        membership.2.trans shiftBounded
      have pathRead := burnolSourceFeatureCompletionPhysicalMap_orbit
        source segment z positive belowHalf base baseNonnegative baseBounded
      change rangeProjection
          (burnolSourceFeatureCompletionPhysicalMap z
            (quarterFeatureCompletionRightResolventIntegrand z
              (burnolSourceQuarterCompletionValue source z positive belowHalf)
              base)) =
        burnolSourceFeatureCompletionPhysicalMap z
          (quarterFeatureCompletionRightResolventIntegrand z
            (burnolSourceQuarterCompletionValue source z positive belowHalf)
            base)
      rw [pathRead]
      apply burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_eq_self_iff.mpr
      apply burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem
      simpa [burnolCompactCoPoissonGenerator] using
        burnolCompactCoPoissonGenerator_mem_closedRange
          (segment.sourceAt base baseNonnegative baseBounded, (0 : Fin 2))
    _ = _ := by
      rw [physicalMap.integral_comp_comm completionIntegrable]

/-- The generic completion resolvent writes the finite source boundary before
physical projection. -/
theorem burnolSourceQuarterCompletionRightResolvent_sourceBoundary
    (source : burnolCompactAnnulusSource)
    (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (shift : ℝ) (shiftNonnegative : 0 ≤ shift) :
    quarterFeatureCompletionTranslation z shift
        (quarterFeatureCompletionRightResolvent z
          (burnolSourceQuarterCompletionValue source z positive belowHalf)) -
      positiveMellinQuarterRightResolventCharacter z shift •
        quarterFeatureCompletionRightResolvent z
          (burnolSourceQuarterCompletionValue source z positive belowHalf) =
      positiveMellinQuarterRightResolventCharacter z shift •
        burnolSourceQuarterCompletionBoundary
          source z positive belowHalf shift := by
  apply (hilbertAmbientRealization (quarterMellinL2Feature z)).injective
  rw [map_sub, map_smul, map_smul,
    quarterFeatureCompletionTranslation_realization,
    quarterFeatureCompletionRightResolvent_realization,
    burnolSourceQuarterCompletionBoundary_realization]
  unfold burnolSourceQuarterCompletionValue
  rw [hilbertAmbientRealization_source_readback]
  exact positiveMellinQuarterRightResolvent_sourceBoundary
    z rightQuarter _ shift shiftNonnegative

def burnolSourceQuarterRightResolventPhysicalState
    (source : burnolCompactAnnulusSource)
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    BurnolPaAmbientCarrier :=
  burnolSourceFeatureCompletionPhysicalMap z
    (quarterFeatureCompletionRightResolvent z
      (burnolSourceQuarterCompletionValue source z positive belowHalf))

theorem burnolSourceFeatureCompletionPhysicalMap_translation
    (z : ℂ) (shift : ℝ)
    (value : HilbertAmbient (quarterMellinL2Feature z)) :
    burnolSourceFeatureCompletionPhysicalMap z
        (quarterFeatureCompletionTranslation z shift value) =
      burnolEvenAmbientProjection
        (burnolMultiplicativeDilation (-shift / 2)
          (quarterMellinFeatureCompletionEvenAdditive z value)) := by
  unfold burnolSourceFeatureCompletionPhysicalMap
  rw [ContinuousLinearMap.comp_apply,
    quarterMellinFeatureCompletionEvenAdditive_translation]

/-- Projection preservation and the closed-range boundary combine to give
the quotient character equation directly from the stable source orbit. -/
theorem burnolSourceQuarterRightResolvent_orthogonalResidual_eigenlaw
    (source : burnolCompactAnnulusSource)
    (segment : BurnolCompactAnnulusDilationSegment source)
    (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (shift : ℝ) (shiftNonnegative : 0 ≤ shift)
    (shiftBounded : shift ≤ Real.log 16) :
    SourceGeneratedHilbertCokernel.residual burnolCompactCoPoissonLanding
        (burnolSourceFeatureCompletionPhysicalMap z
          (quarterFeatureCompletionTranslation z shift
            (quarterFeatureCompletionRightResolvent z
              (burnolSourceQuarterCompletionValue
                source z positive belowHalf)))) =
      positiveMellinQuarterRightResolventCharacter z shift •
        SourceGeneratedHilbertCokernel.residual burnolCompactCoPoissonLanding
          (burnolSourceQuarterRightResolventPhysicalState
            source z positive belowHalf) := by
  let residual := SourceGeneratedHilbertCokernel.residual
    burnolCompactCoPoissonLanding
  have sourceBoundary := congrArg (burnolSourceFeatureCompletionPhysicalMap z)
    (burnolSourceQuarterCompletionRightResolvent_sourceBoundary
      source z rightQuarter positive belowHalf shift shiftNonnegative)
  have boundaryLanding :=
    burnolSourceQuarterBoundaryPhysicalLanding_mem_closedRange
      source segment z positive belowHalf shift shiftBounded
  have killed : residual
      (positiveMellinQuarterRightResolventCharacter z shift •
        burnolSourceQuarterBoundaryPhysicalLanding
          source z positive belowHalf shift) = 0 := by
    apply (SourceGeneratedHilbertCokernel.residual_eq_zero_iff
      burnolCompactCoPoissonLanding _).mpr
    exact burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _
      boundaryLanding
  apply sub_eq_zero.mp
  calc
    residual
        (burnolSourceFeatureCompletionPhysicalMap z
          (quarterFeatureCompletionTranslation z shift
            (quarterFeatureCompletionRightResolvent z
              (burnolSourceQuarterCompletionValue
                source z positive belowHalf)))) -
        positiveMellinQuarterRightResolventCharacter z shift •
          residual (burnolSourceQuarterRightResolventPhysicalState
            source z positive belowHalf) =
      residual
        (burnolSourceFeatureCompletionPhysicalMap z
            (quarterFeatureCompletionTranslation z shift
              (quarterFeatureCompletionRightResolvent z
                (burnolSourceQuarterCompletionValue
                  source z positive belowHalf))) -
          positiveMellinQuarterRightResolventCharacter z shift •
            burnolSourceQuarterRightResolventPhysicalState
              source z positive belowHalf) := by rw [map_sub, map_smul]
    _ = residual
        (positiveMellinQuarterRightResolventCharacter z shift •
          burnolSourceQuarterBoundaryPhysicalLanding
            source z positive belowHalf shift) := by
      simpa only [map_sub, map_smul,
        burnolSourceQuarterRightResolventPhysicalState,
        burnolSourceQuarterBoundaryPhysicalLanding] using
          congrArg residual sourceBoundary
    _ = 0 := killed

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
