import H0mework.Versions.Y.Arithmetic.BurnolPhysical.QuarterMellinAdditiveRechartAlgebra
import H0mework.Versions.Y.Arithmetic.RiemannAnnulus.CompactCoPoissonQuarterProjection
import H0mework.Versions.Y.Arithmetic.BurnolPhysical.GraphGramBoundary
import H0mework.Realization.Graph.FeatureCompression

/-!
# Bounded quarter-Mellin graph realization in additive Burnol coordinates

The feature-range isometry extends to the feature and graph completions.  A
product realization retains the scalar coordinate, and the actual compact
co-Poisson relation lands in the existing closed range with scalar zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedFunctionalGraphPerfectification
open scoped ENNReal InnerProductSpace

noncomputable section

/-- Bounded extension of the scaled additive rechart over the completion of
the actual quarter-feature range. -/
def quarterMellinFeatureCompletionEvenAdditive (z : ℂ) :
    HilbertAmbient (quarterMellinL2Feature z) →L[ℂ] BurnolL2 :=
  (quarterMellinFeatureRangeEvenAdditiveIsometry z
    ).toContinuousLinearMap.fromCompletion

@[simp] theorem quarterMellinFeatureCompletionEvenAdditive_source
    {z : ℂ} (value : QuarterMellinL2Test z) :
    quarterMellinFeatureCompletionEvenAdditive z
        (canonicalHilbertMap (quarterMellinL2Feature z) value) =
      (2 : ℂ) • quarterMellinAdditiveEvenRechart value := by
  let rangeValue := (quarterMellinL2Feature z).rangeRestrict value
  change (quarterMellinFeatureRangeEvenAdditiveIsometry z
      ).toContinuousLinearMap.fromCompletion
      (rangeValue : HilbertAmbient (quarterMellinL2Feature z)) =
    (2 : ℂ) • quarterMellinAdditiveEvenRechart value
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  exact quarterMellinFeatureRangeEvenAdditiveIsometry_source value

/-- The graph completion maps boundedly to the additive coordinate.  This
map deliberately forgets the graph's scalar measurement coordinate. -/
def quarterMellinGraphCompletionEvenAdditive (z : ℂ) :
    QuarterMellinGraphCompletion z →L[ℂ] BurnolL2 :=
  (quarterMellinFeatureCompletionEvenAdditive z).comp
    (graphToFeatureCompletion
      (quarterMellinL2Feature z) (quarterMellinL2Functional z))

@[simp] theorem quarterMellinGraphCompletionEvenAdditive_source
    {z : ℂ} (value : QuarterMellinL2Test z) :
    quarterMellinGraphCompletionEvenAdditive z
        (quarterMellinGraphDenseSourceMap z value) =
      (2 : ℂ) • quarterMellinAdditiveEvenRechart value := by
  unfold quarterMellinGraphCompletionEvenAdditive
    quarterMellinGraphDenseSourceMap
    SourceGeneratedFunctionalGraphCokernel.graphSourceMap
  rw [ContinuousLinearMap.comp_apply,
    graphToFeatureCompletion_source_readback,
    quarterMellinFeatureCompletionEvenAdditive_source]

/-- Bounded graph realization retaining both the scaled additive coordinate
and the original scalar measurement.  The first coordinate is not asserted
to lie in the Burnol physical face. -/
def quarterMellinGraphCompletionEvenAdditiveWithScalar (z : ℂ) :
    QuarterMellinGraphCompletion z →L[ℂ]
      WithLp 2 (BurnolL2 × ℂ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ BurnolL2 ℂ
      ).symm.toContinuousLinearMap.comp
    ((quarterMellinGraphCompletionEvenAdditive z).prod
      (graphHilbertFunctional
        (quarterMellinL2Feature z) (quarterMellinL2Functional z)))

@[simp] theorem quarterMellinGraphCompletionEvenAdditiveWithScalar_source
    {z : ℂ} (value : QuarterMellinL2Test z) :
    quarterMellinGraphCompletionEvenAdditiveWithScalar z
        (quarterMellinGraphDenseSourceMap z value) =
      WithLp.toLp 2
        ((2 : ℂ) • quarterMellinAdditiveEvenRechart value,
          quarterMellinL2Functional z value) := by
  unfold quarterMellinGraphCompletionEvenAdditiveWithScalar
  rw [ContinuousLinearMap.comp_apply]
  change WithLp.toLp 2
      (quarterMellinGraphCompletionEvenAdditive z
          (quarterMellinGraphDenseSourceMap z value),
        graphHilbertFunctional
          (quarterMellinL2Feature z) (quarterMellinL2Functional z)
          (quarterMellinGraphDenseSourceMap z value)) = _
  rw [quarterMellinGraphCompletionEvenAdditive_source]
  unfold quarterMellinGraphDenseSourceMap
    SourceGeneratedFunctionalGraphCokernel.graphSourceMap
  rw [graphHilbertFunctional_source_readback]

/-- The actual compact co-Poisson relation maps to its additive physical
state while its graph scalar vanishes at the same modified-WeakFE zero. -/
theorem quarterMellinGraphCompletionEvenAdditiveWithScalar_compactRelation
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (zero : riemannZeta (2 * z) = 0)
    (source : burnolCompactAnnulusSource) :
    quarterMellinGraphCompletionEvenAdditiveWithScalar z
        (quarterMellinGraphDenseSourceMap z
          (coPoissonQuarterMellinConvergentMap z positive belowHalf source.1)) =
      WithLp.toLp 2
        ((2 : ℂ) • (burnolCompactAdditivePhysicalState source : BurnolL2), 0) := by
  rw [quarterMellinGraphCompletionEvenAdditiveWithScalar_source,
    compactQuarterMellinAdditiveEvenRechart_eq]
  have functionalZero := LinearMap.congr_fun
    (quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      z positive belowHalf zero) source.1
  have functionalZero' :
      quarterMellinL2Functional z
          (coPoissonQuarterMellinConvergentMap z positive belowHalf source.1) = 0 := by
    simpa using functionalZero
  rw [functionalZero']
  rfl

/-- Direct closed-range consumer for the compact relation source.  The
product target records that the scalar coordinate was retained and killed
by the same zeta-zero occurrence, rather than silently forgotten. -/
theorem quarterMellinGraphCompactRelation_additive_mem_closedRange
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (zero : riemannZeta (2 * z) = 0)
    (source : burnolCompactAnnulusSource) :
    (2 : ℂ) • burnolCompactAdditivePhysicalState source ∈
        burnolCompactCoPoissonClosedRange ∧
      (quarterMellinGraphCompletionEvenAdditiveWithScalar z
          (quarterMellinGraphDenseSourceMap z
            (coPoissonQuarterMellinConvergentMap z positive belowHalf source.1))).fst =
        (2 : ℂ) • (burnolCompactAdditivePhysicalState source : BurnolL2) ∧
      (quarterMellinGraphCompletionEvenAdditiveWithScalar z
          (quarterMellinGraphDenseSourceMap z
            (coPoissonQuarterMellinConvergentMap z positive belowHalf source.1))).snd = 0 := by
  have landing :=
    quarterMellinGraphCompletionEvenAdditiveWithScalar_compactRelation
      z positive belowHalf zero source
  refine ⟨?_, ?_, ?_⟩
  · exact burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem
      (2 : ℂ) (by
        simpa [burnolCompactCoPoissonGenerator] using
          burnolCompactCoPoissonGenerator_mem_closedRange
            (source, (0 : Fin 2)))
  · rw [landing]
    rfl
  · rw [landing]
    rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
