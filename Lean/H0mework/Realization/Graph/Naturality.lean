import Mathlib.Analysis.Normed.Operator.Prod
import H0mework.Realization.Graph.Completion

/-!
# Naturality of source-generated functional graph completion

A source linear map, a continuous Hilbert map, and the two actual commuting
squares generate maps on graph targets, graph ranges, and their completions.
No finite, projective, determinant, isometry, or surjectivity hypothesis is
used.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFunctionalGraphPerfectification

open SourceGeneratedComplexFeaturePerfectification

noncomputable section

universe c c' c'' h h' h''

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {C' : Type c'} [AddCommGroup C'] [Module ℂ C']
variable {C'' : Type c''} [AddCommGroup C''] [Module ℂ C'']
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {H' : Type h'} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
variable {H'' : Type h''} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']

/-- Same-source morphism of a feature/functional pair.  The functional square
is contravariant, while the source and Hilbert maps point forward. -/
structure GraphSourceMorphism
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (feature' : C' →ₗ[ℂ] H') (functional' : C' →ₗ[ℂ] ℂ) where
  sourceMap : C →ₗ[ℂ] C'
  hilbertMap : H →L[ℂ] H'
  feature_commutes :
    hilbertMap.toLinearMap.comp feature = feature'.comp sourceMap
  functional_commutes :
    functional'.comp sourceMap = functional

/-- Map of `L²` graph targets induced by the Hilbert map and the identity
on the functional coordinate. -/
def graphTargetMap
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    (morphism : GraphSourceMorphism feature functional feature' functional') :
    GraphTarget H →L[ℂ] GraphTarget H' :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H' ℂ).symm.toContinuousLinearMap.comp
    ((morphism.hilbertMap.prodMap (ContinuousLinearMap.id ℂ ℂ)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).toContinuousLinearMap)

@[simp]
theorem graphTargetMap_fst
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    (morphism : GraphSourceMorphism feature functional feature' functional')
    (value : GraphTarget H) :
    (graphTargetMap morphism value).fst = morphism.hilbertMap value.fst :=
  rfl

@[simp]
theorem graphTargetMap_snd
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    (morphism : GraphSourceMorphism feature functional feature' functional')
    (value : GraphTarget H) :
    (graphTargetMap morphism value).snd = value.snd :=
  rfl

theorem graphTargetMap_source
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    (morphism : GraphSourceMorphism feature functional feature' functional')
    (value : C) :
    graphTargetMap morphism (graphFeature feature functional value) =
      graphFeature feature' functional' (morphism.sourceMap value) := by
  apply (WithLp.linearEquiv 2 ℂ (H' × ℂ)).injective
  apply Prod.ext
  · change morphism.hilbertMap (feature value) =
      feature' (morphism.sourceMap value)
    exact LinearMap.congr_fun morphism.feature_commutes value
  · change functional value = functional' (morphism.sourceMap value)
    exact (LinearMap.congr_fun morphism.functional_commutes value).symm

theorem graphTargetMap_maps_range
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    (morphism : GraphSourceMorphism feature functional feature' functional')
    (value : LinearMap.range (graphFeature feature functional)) :
    graphTargetMap morphism value.1 ∈
      LinearMap.range (graphFeature feature' functional') := by
  obtain ⟨source, source_eq⟩ := value.2
  refine ⟨morphism.sourceMap source, ?_⟩
  rw [← graphTargetMap_source morphism source, source_eq]

/-- Induced map of the actual graph ranges. -/
def graphRangeMap
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    (morphism : GraphSourceMorphism feature functional feature' functional') :
    LinearMap.range (graphFeature feature functional) →L[ℂ]
      LinearMap.range (graphFeature feature' functional') :=
  ((graphTargetMap morphism).domRestrict
      (LinearMap.range (graphFeature feature functional))).codRestrict
    (LinearMap.range (graphFeature feature' functional'))
    (graphTargetMap_maps_range morphism)

@[simp]
theorem graphRangeMap_apply
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    (morphism : GraphSourceMorphism feature functional feature' functional')
    (value : LinearMap.range (graphFeature feature functional)) :
    (graphRangeMap morphism value : GraphTarget H') =
      graphTargetMap morphism value.1 :=
  rfl

/-- The induced continuous map between the canonical graph completions. -/
def graphCompletionMap
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    (morphism : GraphSourceMorphism feature functional feature' functional') :
    GraphHilbertAmbient feature functional →L[ℂ]
      GraphHilbertAmbient feature' functional' :=
  ((graphRangeEmbedding feature' functional').comp
      (graphRangeMap morphism)).extend
    (graphRangeEmbedding feature functional)

@[simp]
theorem graphCompletionMap_range_readback
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    (morphism : GraphSourceMorphism feature functional feature' functional')
    (value : LinearMap.range (graphFeature feature functional)) :
    graphCompletionMap morphism
        (graphRangeEmbedding feature functional value) =
      graphRangeEmbedding feature' functional'
        (graphRangeMap morphism value) := by
  rw [graphCompletionMap, ContinuousLinearMap.extend_eq
    ((graphRangeEmbedding feature' functional').comp
      (graphRangeMap morphism))
    (graphRangeEmbedding_denseRange feature functional)
    (graphRangeEmbedding_isUniformInducing feature functional)]
  rfl

@[simp]
theorem graphCompletionMap_source_readback
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    (morphism : GraphSourceMorphism feature functional feature' functional')
    (value : C) :
    graphCompletionMap morphism
        (canonicalHilbertMap (graphFeature feature functional) value) =
      canonicalHilbertMap (graphFeature feature' functional')
        (morphism.sourceMap value) := by
  change graphCompletionMap morphism
      (graphRangeEmbedding feature functional
        ((graphFeature feature functional).rangeRestrict value)) = _
  rw [graphCompletionMap_range_readback]
  change graphRangeEmbedding feature' functional'
      (graphRangeMap morphism
        ((graphFeature feature functional).rangeRestrict value)) =
    graphRangeEmbedding feature' functional'
      ((graphFeature feature' functional').rangeRestrict
        (morphism.sourceMap value))
  congr 1
  apply Subtype.ext
  exact graphTargetMap_source morphism value

/-- The canonical continuous functional coordinate is natural along the
generated completion map.  This consumes `functional_commutes`; it does not
derive that square. -/
theorem graphHilbertFunctional_naturality
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    (morphism : GraphSourceMorphism feature functional feature' functional')
    (value : GraphHilbertAmbient feature functional) :
    graphHilbertFunctional feature' functional'
        (graphCompletionMap morphism value) =
      graphHilbertFunctional feature functional value := by
  let left : GraphHilbertAmbient feature functional →L[ℂ] ℂ :=
    (graphHilbertFunctional feature' functional').comp
      (graphCompletionMap morphism)
  let right : GraphHilbertAmbient feature functional →L[ℂ] ℂ :=
    graphHilbertFunctional feature functional
  have maps_eq : left = right := by
    apply ContinuousLinearMap.ext
    intro point
    have functions_eq :=
      (graphCanonicalHilbertMap_denseRange feature functional).equalizer
        left.continuous right.continuous (by
          funext source
          change graphHilbertFunctional feature' functional'
              (graphCompletionMap morphism
                (canonicalHilbertMap
                  (graphFeature feature functional) source)) =
            graphHilbertFunctional feature functional
              (canonicalHilbertMap
                (graphFeature feature functional) source)
          rw [graphCompletionMap_source_readback,
            graphHilbertFunctional_source_readback,
            graphHilbertFunctional_source_readback]
          exact LinearMap.congr_fun morphism.functional_commutes source)
    simpa using congrFun functions_eq point
  exact congrArg (fun map :
    GraphHilbertAmbient feature functional →L[ℂ] ℂ => map value) maps_eq

namespace GraphSourceMorphism

def identity
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    GraphSourceMorphism feature functional feature functional where
  sourceMap := LinearMap.id
  hilbertMap := ContinuousLinearMap.id ℂ H
  feature_commutes := by rfl
  functional_commutes := by rfl

def comp
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    {feature'' : C'' →ₗ[ℂ] H''} {functional'' : C'' →ₗ[ℂ] ℂ}
    (first : GraphSourceMorphism feature functional feature' functional')
    (second : GraphSourceMorphism feature' functional' feature'' functional'') :
    GraphSourceMorphism feature functional feature'' functional'' where
  sourceMap := second.sourceMap.comp first.sourceMap
  hilbertMap := second.hilbertMap.comp first.hilbertMap
  feature_commutes := by
    apply LinearMap.ext
    intro value
    change second.hilbertMap (first.hilbertMap (feature value)) =
      feature'' (second.sourceMap (first.sourceMap value))
    have first_commutes := LinearMap.congr_fun first.feature_commutes value
    have second_commutes := LinearMap.congr_fun second.feature_commutes
      (first.sourceMap value)
    change first.hilbertMap (feature value) =
      feature' (first.sourceMap value) at first_commutes
    change second.hilbertMap (feature' (first.sourceMap value)) =
      feature'' (second.sourceMap (first.sourceMap value)) at second_commutes
    rw [first_commutes, second_commutes]
  functional_commutes := by
    apply LinearMap.ext
    intro value
    change functional'' (second.sourceMap (first.sourceMap value)) =
      functional value
    have second_commutes := LinearMap.congr_fun second.functional_commutes
      (first.sourceMap value)
    have first_commutes := LinearMap.congr_fun first.functional_commutes value
    exact second_commutes.trans first_commutes

@[simp]
theorem graphCompletionMap_identity
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    graphCompletionMap (identity feature functional) =
      ContinuousLinearMap.id ℂ (GraphHilbertAmbient feature functional) := by
  apply ContinuousLinearMap.ext
  intro point
  have functions_eq :=
    (graphCanonicalHilbertMap_denseRange feature functional).equalizer
      (graphCompletionMap (identity feature functional)).continuous
      (ContinuousLinearMap.id ℂ
        (GraphHilbertAmbient feature functional)).continuous (by
          funext source
          change graphCompletionMap (identity feature functional)
              (canonicalHilbertMap
                (graphFeature feature functional) source) =
            canonicalHilbertMap (graphFeature feature functional) source
          rw [graphCompletionMap_source_readback]
          rfl)
  simpa using congrFun functions_eq point

@[simp]
theorem graphCompletionMap_comp
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
    {feature'' : C'' →ₗ[ℂ] H''} {functional'' : C'' →ₗ[ℂ] ℂ}
    (first : GraphSourceMorphism feature functional feature' functional')
    (second : GraphSourceMorphism feature' functional' feature'' functional'') :
    graphCompletionMap (comp first second) =
      (graphCompletionMap second).comp (graphCompletionMap first) := by
  apply ContinuousLinearMap.ext
  intro point
  have functions_eq :=
    (graphCanonicalHilbertMap_denseRange feature functional).equalizer
      (graphCompletionMap (comp first second)).continuous
      ((graphCompletionMap second).comp
        (graphCompletionMap first)).continuous (by
          funext source
          change graphCompletionMap (comp first second)
              (canonicalHilbertMap
                (graphFeature feature functional) source) =
            graphCompletionMap second
              (graphCompletionMap first
                (canonicalHilbertMap
                  (graphFeature feature functional) source))
          rw [graphCompletionMap_source_readback,
            graphCompletionMap_source_readback,
            graphCompletionMap_source_readback]
          rfl)
  simpa using congrFun functions_eq point

end GraphSourceMorphism

end

end SourceGeneratedFunctionalGraphPerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
