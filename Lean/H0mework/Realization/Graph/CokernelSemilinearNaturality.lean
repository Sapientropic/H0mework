import H0mework.Realization.Graph.FunctionalSemilinearNaturality
import H0mework.Realization.Graph.Cokernel

/-!
# Semilinear naturality of the functional graph cokernel

A semilinear graph-source morphism and a semilinear map of the actual relation
families generate the map on closed-relation quotients.  The quotient map is
obtained from the generated graph-completion map; no quotient map or quotient
class identification is supplied by a caller.
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

universe c c' r r' h h'

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {C' : Type c'} [AddCommGroup C'] [Module ℂ C']
variable {Rel : Type r} [AddCommGroup Rel] [Module ℂ Rel]
variable {Rel' : Type r'} [AddCommGroup Rel'] [Module ℂ Rel']
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {H' : Type h'} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
variable {σ : ℂ →+* ℂ}

/-- Same-source semilinear morphism of functional graphs together with their
actual relation families.  The relation square is the only extra input. -/
structure SemilinearRelationGraphSourceMorphism
    (σ : ℂ →+* ℂ)
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (relation : Rel →ₗ[ℂ] C)
    (feature' : C' →ₗ[ℂ] H') (functional' : C' →ₗ[ℂ] ℂ)
    (relation' : Rel' →ₗ[ℂ] C') where
  graphMorphism : SemilinearGraphSourceMorphism
    σ feature functional feature' functional'
  relationMap : Rel →ₛₗ[σ] Rel'
  relation_commutes : ∀ value,
    graphMorphism.sourceMap (relation value) = relation' (relationMap value)

namespace SemilinearRelationGraphSourceMorphism

variable {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
variable {relation : Rel →ₗ[ℂ] C}
variable {feature' : C' →ₗ[ℂ] H'} {functional' : C' →ₗ[ℂ] ℂ}
variable {relation' : Rel' →ₗ[ℂ] C'}

/-- The generated semilinear completion map carries each actual relation to
the corresponding target relation. -/
theorem graphCompletionMap_relation
    (morphism : SemilinearRelationGraphSourceMorphism
      σ feature functional relation feature' functional' relation')
    (value : Rel) :
    semilinearGraphCompletionMap morphism.graphMorphism
        (relationGraphMap feature functional relation value) =
      relationGraphMap feature' functional' relation'
        (morphism.relationMap value) := by
  change semilinearGraphCompletionMap morphism.graphMorphism
      (SourceGeneratedComplexFeaturePerfectification.canonicalHilbertMap
        (graphFeature feature functional) (relation value)) =
    SourceGeneratedComplexFeaturePerfectification.canonicalHilbertMap
      (graphFeature feature' functional')
      (relation' (morphism.relationMap value))
  rw [semilinearGraphCompletionMap_source_readback]
  exact congrArg
    (SourceGeneratedComplexFeaturePerfectification.canonicalHilbertMap
      (graphFeature feature' functional'))
    (morphism.relation_commutes value)

/-- The generated semilinear completion map sends the entire closed relation
range into the target closed relation range. -/
theorem graphCompletionMap_mem_closedRange
    (morphism : SemilinearRelationGraphSourceMorphism
      σ feature functional relation feature' functional' relation')
    {point : GraphCompletion feature functional}
    (hpoint : point ∈ closedRange
      (relationGraphMap feature functional relation)) :
    semilinearGraphCompletionMap morphism.graphMorphism point ∈
      closedRange (relationGraphMap feature' functional' relation') := by
  have mapsRange : Set.MapsTo
      (semilinearGraphCompletionMap morphism.graphMorphism)
      ((LinearMap.range (relationGraphMap feature functional relation) :
        Submodule ℂ (GraphCompletion feature functional)) : Set _)
      (closedRange (relationGraphMap feature' functional' relation') : Set _) := by
    rintro _ ⟨value, rfl⟩
    rw [morphism.graphCompletionMap_relation]
    exact (LinearMap.range
      (relationGraphMap feature' functional' relation')).le_topologicalClosure
      ⟨morphism.relationMap value, rfl⟩
  exact mapsRange.closure_left
    (semilinearGraphCompletionMap morphism.graphMorphism).continuous
    (closedRange (relationGraphMap feature' functional' relation')).isClosed
    hpoint

/-- The native continuous semilinear map of the generated closed-relation
quotients. -/
def quotientMap
    (morphism : SemilinearRelationGraphSourceMorphism
      σ feature functional relation feature' functional' relation') :
    ClosedRangeQuotient feature functional relation →SL[σ]
      ClosedRangeQuotient feature' functional' relation' :=
  (closedRange
    (relationGraphMap feature functional relation)).toSubmodule.liftQL
    ((quotientClass
      (relationGraphMap feature' functional' relation')).comp
      (semilinearGraphCompletionMap morphism.graphMorphism)) (by
        intro point hpoint
        change quotientClass (relationGraphMap feature' functional' relation')
          (semilinearGraphCompletionMap morphism.graphMorphism point) = 0
        rw [quotientClass_eq_zero_iff]
        exact morphism.graphCompletionMap_mem_closedRange hpoint)

@[simp]
theorem quotientMap_quotientClass
    (morphism : SemilinearRelationGraphSourceMorphism
      σ feature functional relation feature' functional' relation')
    (point : GraphCompletion feature functional) :
    morphism.quotientMap
        (quotientClass (relationGraphMap feature functional relation) point) =
      quotientClass (relationGraphMap feature' functional' relation')
        (semilinearGraphCompletionMap morphism.graphMorphism point) := by
  unfold quotientMap
  rw [Submodule.liftQL_apply]
  change (closedRange
    (relationGraphMap feature functional relation)).toSubmodule.liftQ _ _
      (Submodule.Quotient.mk point) = _
  rw [Submodule.liftQ_apply]
  rfl

/-- The semilinear quotient map reads the same generated source occurrence. -/
@[simp]
theorem quotientMap_source_readback
    (morphism : SemilinearRelationGraphSourceMorphism
      σ feature functional relation feature' functional' relation')
    (value : C) :
    morphism.quotientMap
        (canonicalSourceMap feature functional relation value) =
      canonicalSourceMap feature' functional' relation'
        (morphism.graphMorphism.sourceMap value) := by
  change morphism.quotientMap
      (quotientClass (relationGraphMap feature functional relation)
        (graphSourceMap feature functional value)) = _
  rw [quotientMap_quotientClass]
  change quotientClass (relationGraphMap feature' functional' relation')
      (semilinearGraphCompletionMap morphism.graphMorphism
        (SourceGeneratedComplexFeaturePerfectification.canonicalHilbertMap
          (graphFeature feature functional) value)) = _
  rw [semilinearGraphCompletionMap_source_readback]
  rfl

/-- The descended functional is semilinearly natural on every quotient class.
The target functional is read after the quotient map and the source functional
is read before the generated scalar action. -/
@[simp]
theorem descendedFunctional_quotientMap
    (morphism : SemilinearRelationGraphSourceMorphism
      σ feature functional relation feature' functional' relation')
    (annihilates : functional.comp relation = 0)
    (annihilates' : functional'.comp relation' = 0)
    (quotient : ClosedRangeQuotient feature functional relation) :
    descendedFunctional feature' functional' relation' annihilates'
        (morphism.quotientMap quotient) =
      morphism.graphMorphism.scalarMap
        (descendedFunctional feature functional relation annihilates quotient) := by
  induction quotient using Submodule.Quotient.induction_on with
  | _ point =>
      change descendedFunctional feature' functional' relation' annihilates'
          (morphism.quotientMap
            (quotientClass
              (relationGraphMap feature functional relation) point)) =
        morphism.graphMorphism.scalarMap
          (descendedFunctional feature functional relation annihilates
            (quotientClass
              (relationGraphMap feature functional relation) point))
      rw [quotientMap_quotientClass]
      change graphHilbertFunctional feature' functional'
          (semilinearGraphCompletionMap morphism.graphMorphism point) =
        morphism.graphMorphism.scalarMap
          (graphHilbertFunctional feature functional point)
      exact graphHilbertFunctional_semilinear_naturality
        morphism.graphMorphism point

/-- Map-level form of semilinear descended-functional naturality. -/
theorem descendedFunctional_naturality
    (morphism : SemilinearRelationGraphSourceMorphism
      σ feature functional relation feature' functional' relation')
    (annihilates : functional.comp relation = 0)
    (annihilates' : functional'.comp relation' = 0) :
    (descendedFunctional feature' functional' relation' annihilates').comp
        morphism.quotientMap =
      morphism.graphMorphism.scalarMap.comp
        (descendedFunctional feature functional relation annihilates) := by
  apply ContinuousLinearMap.ext
  intro quotient
  exact morphism.descendedFunctional_quotientMap
    annihilates annihilates' quotient

end SemilinearRelationGraphSourceMorphism

end

end SourceGeneratedFunctionalGraphCokernel
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
