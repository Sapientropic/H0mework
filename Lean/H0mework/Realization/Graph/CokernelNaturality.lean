import H0mework.Realization.Graph.Cokernel
import H0mework.Realization.Graph.Naturality

/-!
# Naturality of the functional graph cokernel

A graph-source morphism together with an actual relation map and relation square sends the closed
relation range into the target closed relation range. It therefore descends continuously to the
generated quotients and preserves both canonical source classes and descended functionals. No
injectivity, surjectivity, isometry, finiteness, closed-range, or determinant premise is used.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFunctionalGraphCokernel

open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedHilbertCokernel

noncomputable section

universe c c' c'' r r' r'' h h' h''

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {C' : Type c'} [AddCommGroup C'] [Module ℂ C']
variable {C'' : Type c''} [AddCommGroup C''] [Module ℂ C'']
variable {Rel : Type r} [AddCommGroup Rel] [Module ℂ Rel]
variable {Rel' : Type r'} [AddCommGroup Rel'] [Module ℂ Rel']
variable {Rel'' : Type r''} [AddCommGroup Rel''] [Module ℂ Rel'']
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {H' : Type h'} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
variable {H'' : Type h''} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']

/-- Same-source morphism of functional graphs and their actual relation families. -/
structure RelationGraphSourceMorphism
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) (relation : Rel →ₗ[ℂ] C)
    (feature' : C' →ₗ[ℂ] H') (functional' : C' →ₗ[ℂ] ℂ)
    (relation' : Rel' →ₗ[ℂ] C') where
  graphMorphism : GraphSourceMorphism feature functional feature' functional'
  relationMap : Rel →ₗ[ℂ] Rel'
  relation_commutes :
    graphMorphism.sourceMap.comp relation = relation'.comp relationMap

namespace RelationGraphSourceMorphism

variable {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ} {relation : Rel →ₗ[ℂ] C}
variable {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
variable {relation' : Rel' →ₗ[ℂ] C'}

/-- The generated completion map carries each relation to its target relation. -/
theorem graphCompletionMap_relation
    (morphism : RelationGraphSourceMorphism
      feature functional relation feature' functional' relation') (value : Rel) :
    graphCompletionMap morphism.graphMorphism
        (relationGraphMap feature functional relation value) =
      relationGraphMap feature' functional' relation' (morphism.relationMap value) := by
  change graphCompletionMap morphism.graphMorphism
      (SourceGeneratedComplexFeaturePerfectification.canonicalHilbertMap
        (graphFeature feature functional) (relation value)) =
    SourceGeneratedComplexFeaturePerfectification.canonicalHilbertMap
      (graphFeature feature' functional') (relation' (morphism.relationMap value))
  rw [graphCompletionMap_source_readback]
  apply congrArg (SourceGeneratedComplexFeaturePerfectification.canonicalHilbertMap
    (graphFeature feature' functional'))
  simpa only [LinearMap.comp_apply] using
    LinearMap.congr_fun morphism.relation_commutes value

/-- The completion map sends the full closed relation range into the target one. -/
theorem graphCompletionMap_mem_closedRange
    (morphism : RelationGraphSourceMorphism
      feature functional relation feature' functional' relation')
    {point : GraphCompletion feature functional}
    (hpoint : point ∈ closedRange (relationGraphMap feature functional relation)) :
    graphCompletionMap morphism.graphMorphism point ∈
      closedRange (relationGraphMap feature' functional' relation') := by
  have mapsRange : Set.MapsTo (graphCompletionMap morphism.graphMorphism)
      ((LinearMap.range (relationGraphMap feature functional relation) :
        Submodule ℂ (GraphCompletion feature functional)) : Set _)
      (closedRange (relationGraphMap feature' functional' relation') : Set _) := by
    rintro _ ⟨value, rfl⟩
    rw [morphism.graphCompletionMap_relation]
    exact (LinearMap.range (relationGraphMap feature' functional' relation')).le_topologicalClosure
      ⟨morphism.relationMap value, rfl⟩
  exact mapsRange.closure_left
    (graphCompletionMap morphism.graphMorphism).continuous
    (closedRange (relationGraphMap feature' functional' relation')).isClosed hpoint

/-- The native continuous map of the generated closed-range quotients. -/
def quotientMap
    (morphism : RelationGraphSourceMorphism
      feature functional relation feature' functional' relation') :
    ClosedRangeQuotient feature functional relation →L[ℂ]
      ClosedRangeQuotient feature' functional' relation' :=
  (closedRange (relationGraphMap feature functional relation)).toSubmodule.liftQL
    ((quotientClass (relationGraphMap feature' functional' relation')).comp
      (graphCompletionMap morphism.graphMorphism)) (by
        intro point hpoint
        change quotientClass (relationGraphMap feature' functional' relation')
          (graphCompletionMap morphism.graphMorphism point) = 0
        rw [quotientClass_eq_zero_iff]
        exact morphism.graphCompletionMap_mem_closedRange hpoint)

@[simp]
theorem quotientMap_quotientClass
    (morphism : RelationGraphSourceMorphism
      feature functional relation feature' functional' relation')
    (point : GraphCompletion feature functional) :
    morphism.quotientMap
        (quotientClass (relationGraphMap feature functional relation) point) =
      quotientClass (relationGraphMap feature' functional' relation')
        (graphCompletionMap morphism.graphMorphism point) := by
  unfold quotientMap
  rw [Submodule.liftQL_apply]
  change (closedRange (relationGraphMap feature functional relation)).toSubmodule.liftQ _ _
      (Submodule.Quotient.mk point) = _
  rw [Submodule.liftQ_apply]
  rfl

/-- The quotient map commutes with the canonical source maps. -/
@[simp]
theorem quotientMap_source_readback
    (morphism : RelationGraphSourceMorphism
      feature functional relation feature' functional' relation') (value : C) :
    morphism.quotientMap (canonicalSourceMap feature functional relation value) =
      canonicalSourceMap feature' functional' relation'
        (morphism.graphMorphism.sourceMap value) := by
  change morphism.quotientMap
      (quotientClass (relationGraphMap feature functional relation)
        (graphSourceMap feature functional value)) = _
  rw [quotientMap_quotientClass]
  change quotientClass (relationGraphMap feature' functional' relation')
      (graphCompletionMap morphism.graphMorphism
        (SourceGeneratedComplexFeaturePerfectification.canonicalHilbertMap
          (graphFeature feature functional) value)) = _
  rw [graphCompletionMap_source_readback]
  rfl

theorem quotientMap_comp_source
    (morphism : RelationGraphSourceMorphism
      feature functional relation feature' functional' relation') :
    morphism.quotientMap.toLinearMap.comp
        (canonicalSourceMap feature functional relation) =
      (canonicalSourceMap feature' functional' relation').comp
        morphism.graphMorphism.sourceMap := by
  ext value
  exact morphism.quotientMap_source_readback value

/-- The descended functional is natural along the generated quotient map. -/
theorem descendedFunctional_naturality
    (morphism : RelationGraphSourceMorphism
      feature functional relation feature' functional' relation')
    (annihilates : functional.comp relation = 0)
    (annihilates' : functional'.comp relation' = 0) :
    (descendedFunctional feature' functional' relation' annihilates').comp
        morphism.quotientMap =
      descendedFunctional feature functional relation annihilates := by
  apply descendedFunctional_unique feature functional relation annihilates
  ext value
  change descendedFunctional feature' functional' relation' annihilates'
      (morphism.quotientMap
        (canonicalSourceMap feature functional relation value)) = functional value
  rw [morphism.quotientMap_source_readback,
    descendedFunctional_source_readback]
  exact LinearMap.congr_fun morphism.graphMorphism.functional_commutes value

@[simp]
theorem descendedFunctional_quotientMap
    (morphism : RelationGraphSourceMorphism
      feature functional relation feature' functional' relation')
    (annihilates : functional.comp relation = 0)
    (annihilates' : functional'.comp relation' = 0)
    (quotient : ClosedRangeQuotient feature functional relation) :
    descendedFunctional feature' functional' relation' annihilates'
        (morphism.quotientMap quotient) =
      descendedFunctional feature functional relation annihilates quotient := by
  exact congrArg (fun map :
      ClosedRangeQuotient feature functional relation →L[ℂ] ℂ => map quotient)
    (morphism.descendedFunctional_naturality annihilates annihilates')

def identity
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) (relation : Rel →ₗ[ℂ] C) :
    RelationGraphSourceMorphism feature functional relation feature functional relation where
  graphMorphism := GraphSourceMorphism.identity feature functional
  relationMap := LinearMap.id
  relation_commutes := rfl

def comp
    {feature'' : C'' →ₗ[ℂ] H''} {functional'' : C'' →ₗ[ℂ] ℂ}
    {relation'' : Rel'' →ₗ[ℂ] C''}
    (first : RelationGraphSourceMorphism
      feature functional relation feature' functional' relation')
    (second : RelationGraphSourceMorphism
      feature' functional' relation' feature'' functional'' relation'') :
    RelationGraphSourceMorphism
      feature functional relation feature'' functional'' relation'' where
  graphMorphism := GraphSourceMorphism.comp first.graphMorphism second.graphMorphism
  relationMap := second.relationMap.comp first.relationMap
  relation_commutes := by
    apply LinearMap.ext
    intro value
    change second.graphMorphism.sourceMap
        (first.graphMorphism.sourceMap (relation value)) =
      relation'' (second.relationMap (first.relationMap value))
    have firstCommutes := LinearMap.congr_fun first.relation_commutes value
    have secondCommutes := LinearMap.congr_fun second.relation_commutes
      (first.relationMap value)
    change first.graphMorphism.sourceMap (relation value) =
      relation' (first.relationMap value) at firstCommutes
    change second.graphMorphism.sourceMap (relation' (first.relationMap value)) =
      relation'' (second.relationMap (first.relationMap value)) at secondCommutes
    rw [firstCommutes, secondCommutes]

@[simp]
theorem quotientMap_identity
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) (relation : Rel →ₗ[ℂ] C) :
    (identity feature functional relation).quotientMap =
      ContinuousLinearMap.id ℂ (ClosedRangeQuotient feature functional relation) := by
  apply ContinuousLinearMap.ext
  intro quotient
  induction quotient using Submodule.Quotient.induction_on with
  | _ point =>
      change (identity feature functional relation).quotientMap
          (quotientClass (relationGraphMap feature functional relation) point) =
        quotientClass (relationGraphMap feature functional relation) point
      rw [quotientMap_quotientClass]
      change quotientClass (relationGraphMap feature functional relation)
          (graphCompletionMap (GraphSourceMorphism.identity feature functional) point) =
        quotientClass (relationGraphMap feature functional relation) point
      rw [GraphSourceMorphism.graphCompletionMap_identity]
      rfl

@[simp]
theorem quotientMap_comp
    {feature'' : C'' →ₗ[ℂ] H''} {functional'' : C'' →ₗ[ℂ] ℂ}
    {relation'' : Rel'' →ₗ[ℂ] C''}
    (first : RelationGraphSourceMorphism
      feature functional relation feature' functional' relation')
    (second : RelationGraphSourceMorphism
      feature' functional' relation' feature'' functional'' relation'') :
    (comp first second).quotientMap =
      second.quotientMap.comp first.quotientMap := by
  apply ContinuousLinearMap.ext
  intro quotient
  induction quotient using Submodule.Quotient.induction_on with
  | _ point =>
      change (comp first second).quotientMap
          (quotientClass (relationGraphMap feature functional relation) point) =
        second.quotientMap
          (first.quotientMap
            (quotientClass (relationGraphMap feature functional relation) point))
      rw [quotientMap_quotientClass, quotientMap_quotientClass,
        quotientMap_quotientClass]
      change quotientClass (relationGraphMap feature'' functional'' relation'')
          (graphCompletionMap
            (GraphSourceMorphism.comp first.graphMorphism second.graphMorphism) point) =
        quotientClass (relationGraphMap feature'' functional'' relation'')
          (graphCompletionMap second.graphMorphism
            (graphCompletionMap first.graphMorphism point))
      rw [GraphSourceMorphism.graphCompletionMap_comp]
      rfl

end RelationGraphSourceMorphism

end

end SourceGeneratedFunctionalGraphCokernel
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
