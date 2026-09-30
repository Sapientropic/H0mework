import H0mework.Realization.Graph.Action

/-!
# Canonical compression from functional-graph to feature completion

The graph completion remembers both the coherent feature and one scalar
functional.  Projection to the first coordinate generates a canonical dense
map to the feature-only completion.  A continuous graph coordinate factors
through this map exactly when the source functional has a bounded extension
on the feature completion.  Under a commuting source action, such a factor is
automatically equivariant.  Thus the generalized-dual residual is precisely
the lost scalar coordinate of this canonical compression.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFunctionalGraphPerfectification

open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedTestHilbertGeneralizedDual

noncomputable section

universe c h

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def graphRangeToFeatureRange
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    LinearMap.range (graphFeature feature functional) →L[ℂ]
      LinearMap.range feature :=
  ((WithLp.fstL 2 ℂ H ℂ).comp
    (LinearMap.range (graphFeature feature functional)).subtypeL).codRestrict
      (LinearMap.range feature) (by
        intro value
        obtain ⟨source, sourceEq⟩ := value.2
        refine ⟨source, ?_⟩
        exact congrArg (fun point : GraphTarget H => point.fst) sourceEq)

@[simp] theorem graphRangeToFeatureRange_apply
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (value : LinearMap.range (graphFeature feature functional)) :
    ((graphRangeToFeatureRange feature functional value :
        LinearMap.range feature) : H) = value.1.fst :=
  rfl

def featureRangeEmbedding (feature : C →ₗ[ℂ] H) :
    LinearMap.range feature →L[ℂ] HilbertAmbient feature :=
  (UniformSpace.Completion.toComplₗᵢ :
    LinearMap.range feature →ₗᵢ[ℂ] HilbertAmbient feature
    ).toContinuousLinearMap

/-- Canonical forgetful map from the complete graph carrier to the complete
feature carrier.  Its source is stronger, so the projection is continuous
without a boundedness premise on the scalar coordinate. -/
def graphToFeatureCompletion
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    GraphHilbertAmbient feature functional →L[ℂ] HilbertAmbient feature :=
  ((featureRangeEmbedding feature).comp
    (graphRangeToFeatureRange feature functional)).extend
      (graphRangeEmbedding feature functional)

@[simp] theorem graphToFeatureCompletion_range_readback
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (value : LinearMap.range (graphFeature feature functional)) :
    graphToFeatureCompletion feature functional
        (graphRangeEmbedding feature functional value) =
      featureRangeEmbedding feature
        (graphRangeToFeatureRange feature functional value) := by
  rw [graphToFeatureCompletion, ContinuousLinearMap.extend_eq
    ((featureRangeEmbedding feature).comp
      (graphRangeToFeatureRange feature functional))
    (graphRangeEmbedding_denseRange feature functional)
    (graphRangeEmbedding_isUniformInducing feature functional)]
  rfl

@[simp] theorem graphToFeatureCompletion_source_readback
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (value : C) :
    graphToFeatureCompletion feature functional
        (canonicalHilbertMap (graphFeature feature functional) value) =
      canonicalHilbertMap feature value := by
  change graphToFeatureCompletion feature functional
      (graphRangeEmbedding feature functional
        ((graphFeature feature functional).rangeRestrict value)) = _
  rw [graphToFeatureCompletion_range_readback]
  rfl

theorem graphToFeatureCompletion_denseRange
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    DenseRange (graphToFeatureCompletion feature functional) := by
  have featureDense : DenseRange (canonicalHilbertMap feature) := by
    have dense := UniformSpace.Completion.denseRange_coe.comp
      feature.surjective_rangeRestrict.denseRange
      (UniformSpace.Completion.continuous_coe (LinearMap.range feature))
    simpa [canonicalHilbertMap, Function.comp_def] using dense
  apply Dense.mono _ featureDense
  rintro _ ⟨source, rfl⟩
  refine ⟨canonicalHilbertMap (graphFeature feature functional) source, ?_⟩
  exact graphToFeatureCompletion_source_readback feature functional source

/-- The graph coordinate is faithfully recoverable after forgetting the
scalar axis exactly when it factors through the canonical feature map. -/
structure GraphCoordinateFactorization
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) where
  extension : HilbertAmbient feature →L[ℂ] ℂ
  factorizes : extension.comp (graphToFeatureCompletion feature functional) =
    graphHilbertFunctional feature functional

def GraphCoordinateFactorization.toBoundedExtension
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (factorization : GraphCoordinateFactorization feature functional) :
    BoundedExtension (canonicalHilbertMap feature) functional where
  extension := factorization.extension
  restricts := by
    apply LinearMap.ext
    intro value
    have source := congrArg
      (fun map : GraphHilbertAmbient feature functional →L[ℂ] ℂ =>
        map (canonicalHilbertMap (graphFeature feature functional) value))
      factorization.factorizes
    simpa using source

def GraphCoordinateFactorization.ofBoundedExtension
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (extension : BoundedExtension (canonicalHilbertMap feature) functional) :
    GraphCoordinateFactorization feature functional where
  extension := extension.extension
  factorizes := by
    apply ContinuousLinearMap.ext
    intro point
    have equalOnSource :=
      (graphCanonicalHilbertMap_denseRange feature functional).equalizer
        (extension.extension.comp
          (graphToFeatureCompletion feature functional)).continuous
        (graphHilbertFunctional feature functional).continuous (by
          funext value
          have readback := LinearMap.congr_fun extension.restricts value
          change extension.extension (canonicalHilbertMap feature value) =
            functional value at readback
          simpa using readback)
    exact congrFun equalOnSource point

theorem nonempty_graphCoordinateFactorization_iff_boundedExtension
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    Nonempty (GraphCoordinateFactorization feature functional) ↔
      Nonempty (BoundedExtension (canonicalHilbertMap feature) functional) :=
  ⟨fun ⟨factorization⟩ => ⟨factorization.toBoundedExtension⟩,
    fun ⟨extension⟩ => ⟨GraphCoordinateFactorization.ofBoundedExtension
      extension⟩⟩

/-- A source action on the graph and a generated action on the feature
completion, related on the dense source. -/
structure GraphToFeatureActionComparison
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional) where
  energyAction : HilbertAmbient feature →L[ℂ] HilbertAmbient feature
  source_commutes : ∀ value : C,
    energyAction (canonicalHilbertMap feature value) =
      canonicalHilbertMap feature (covariance.sourceAction value)

theorem GraphToFeatureActionComparison.completion_commutes
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {covariance : GraphCovariance feature functional}
    (comparison : GraphToFeatureActionComparison covariance) :
    comparison.energyAction.comp
        (graphToFeatureCompletion feature functional) =
      (graphToFeatureCompletion feature functional).comp
        (graphHilbertAction covariance) := by
  apply ContinuousLinearMap.ext
  intro point
  have equalOnSource :=
    (graphCanonicalHilbertMap_denseRange feature functional).equalizer
      (comparison.energyAction.comp
        (graphToFeatureCompletion feature functional)).continuous
      ((graphToFeatureCompletion feature functional).comp
        (graphHilbertAction covariance)).continuous (by
          funext value
          change comparison.energyAction
              (graphToFeatureCompletion feature functional
                (canonicalHilbertMap
                  (graphFeature feature functional) value)) =
            graphToFeatureCompletion feature functional
              (graphHilbertAction covariance
                (canonicalHilbertMap
                  (graphFeature feature functional) value))
          rw [graphToFeatureCompletion_source_readback,
            comparison.source_commutes,
            graphHilbertAction_source,
            graphToFeatureCompletion_source_readback])
  exact congrFun equalOnSource point

/-- A graph-coordinate factorization is automatically equivariant: the
action law is forced by the graph eigenlaw and the dense comparison range. -/
def GraphCoordinateFactorization.toEquivariantBoundedExtension
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {covariance : GraphCovariance feature functional}
    (comparison : GraphToFeatureActionComparison covariance)
    (factorization : GraphCoordinateFactorization feature functional) :
    EquivariantBoundedExtension
      (canonicalHilbertMap feature) comparison.energyAction
      covariance.character functional where
  extension := factorization.extension
  eigenlaw := by
    intro value
    let left : HilbertAmbient feature →L[ℂ] ℂ :=
      factorization.extension.comp comparison.energyAction
    let right : HilbertAmbient feature →L[ℂ] ℂ :=
      covariance.character • factorization.extension
    have equalOnGraph : ∀ graphPoint : GraphHilbertAmbient feature functional,
        left (graphToFeatureCompletion feature functional graphPoint) =
          right (graphToFeatureCompletion feature functional graphPoint) := by
      intro graphPoint
      have comparisonSquare := congrArg
        (fun map : GraphHilbertAmbient feature functional →L[ℂ]
          HilbertAmbient feature => map graphPoint)
        comparison.completion_commutes
      have factorAtAction := congrArg
        (fun map : GraphHilbertAmbient feature functional →L[ℂ] ℂ =>
          map (graphHilbertAction covariance graphPoint))
        factorization.factorizes
      have factorAtPoint := congrArg
        (fun map : GraphHilbertAmbient feature functional →L[ℂ] ℂ =>
          map graphPoint) factorization.factorizes
      change comparison.energyAction
          (graphToFeatureCompletion feature functional graphPoint) =
        graphToFeatureCompletion feature functional
          (graphHilbertAction covariance graphPoint) at comparisonSquare
      change factorization.extension
          (graphToFeatureCompletion feature functional
            (graphHilbertAction covariance graphPoint)) =
        graphHilbertFunctional feature functional
          (graphHilbertAction covariance graphPoint) at factorAtAction
      change factorization.extension
          (graphToFeatureCompletion feature functional graphPoint) =
        graphHilbertFunctional feature functional graphPoint at factorAtPoint
      change factorization.extension
          (comparison.energyAction
            (graphToFeatureCompletion feature functional graphPoint)) =
        covariance.character * factorization.extension
          (graphToFeatureCompletion feature functional graphPoint)
      rw [comparisonSquare, factorAtAction,
        graphHilbertFunctional_eigenlaw, factorAtPoint]
    have mapsEqual :=
      (graphToFeatureCompletion_denseRange feature functional).equalizer
        left.continuous right.continuous (by
          funext graphPoint
          exact equalOnGraph graphPoint)
    exact congrFun mapsEqual value
  restricts := factorization.toBoundedExtension.restricts

def GraphCoordinateFactorization.ofEquivariantBoundedExtension
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {covariance : GraphCovariance feature functional}
    {comparison : GraphToFeatureActionComparison covariance}
    (extension : EquivariantBoundedExtension
      (canonicalHilbertMap feature) comparison.energyAction
      covariance.character functional) :
    GraphCoordinateFactorization feature functional :=
  GraphCoordinateFactorization.ofBoundedExtension extension.toBoundedExtension

theorem nonempty_graphCoordinateFactorization_iff_equivariantExtension
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {covariance : GraphCovariance feature functional}
    (comparison : GraphToFeatureActionComparison covariance) :
    Nonempty (GraphCoordinateFactorization feature functional) ↔
      Nonempty (EquivariantBoundedExtension
        (canonicalHilbertMap feature) comparison.energyAction
        covariance.character functional) :=
  ⟨fun ⟨factorization⟩ =>
      ⟨factorization.toEquivariantBoundedExtension comparison⟩,
    fun ⟨extension⟩ =>
      ⟨GraphCoordinateFactorization.ofEquivariantBoundedExtension extension⟩⟩

/-- The exact equivariant extension residual is the obstruction to preserving
the graph coordinate under the canonical graph-to-feature compression. -/
theorem equivariantExtensionResidual_eq_zero_iff_graphCoordinateFactorization
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {covariance : GraphCovariance feature functional}
    (comparison : GraphToFeatureActionComparison covariance) :
    canonicalEquivariantExtensionResidual
        (canonicalHilbertMap feature) comparison.energyAction
        covariance.character functional = 0 ↔
      Nonempty (GraphCoordinateFactorization feature functional) := by
  rw [canonicalEquivariantExtensionResidual_eq_zero_iff]
  exact (nonempty_graphCoordinateFactorization_iff_equivariantExtension
    comparison).symm

end

end SourceGeneratedFunctionalGraphPerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
