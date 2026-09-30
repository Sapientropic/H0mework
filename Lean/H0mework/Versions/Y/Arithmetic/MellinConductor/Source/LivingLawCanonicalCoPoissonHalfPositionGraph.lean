import H0mework.Realization.Graph.CokernelNaturality
import H0mework.Versions.Y.Arithmetic.MellinConductor.Source.LivingLawCanonicalCoPoissonHalfPositionDecay
import H0mework.Versions.Y.Arithmetic.MuntzAction.CoPoissonMuntzGraphCokernel

/-!
# Closed half-position relation graph

The co-Poisson relation is restricted to the source-generated maximal
half-position domain.  Its feature records both the old Quarter-Mellin energy
and the actual half-position output in the Hilbert `L²` product, together with
membership in the closed operator graph.  The bounded first projection gives
the forgetful morphism to the existing Müntz graph; the unbounded operator
itself is never inserted as a bounded map.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace MuntzConductor
namespace HalfPositionSource

open HalfPositionDomain
open SourceGeneratedFunctionalGraphCokernel
open SourceGeneratedFunctionalGraphPerfectification
open scoped SchwartzMap

noncomputable section

def quarterMellinHalfPositionSourceDomain (z : ℂ) :
    Submodule ℂ (QuarterMellinL2Test z) :=
  HalfPositionOperator.domain.comap (quarterMellinL2Feature z)

def coPoissonQuarterHalfPositionRelation
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] quarterMellinHalfPositionSourceDomain z :=
  LinearMap.codRestrict (quarterMellinHalfPositionSourceDomain z)
    (coPoissonQuarterMellinConvergentMap z positive belowHalf)
    (fun test => coPoissonQuarterFeature_mem_halfPositionOperator_domain
      z positive belowHalf test)

def halfPositionRawClosedGraph : ClosedSubmodule ℂ
    (PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy) :=
  ⟨HalfPositionOperator.graph, halfPositionOperator_isClosed⟩

def halfPositionProductHilbertEquiv :
    (PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy) ≃L[ℂ]
      WithLp 2 (PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ
    PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy).symm

abbrev HalfPositionGraphCarrier :=
  WithLp 2 (PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy)

def halfPositionDomainFeature (z : ℂ) :
    quarterMellinHalfPositionSourceDomain z →ₗ[ℂ]
      HalfPositionOperator.domain :=
  LinearMap.codRestrict HalfPositionOperator.domain
    ((quarterMellinL2Feature z).comp
      (quarterMellinHalfPositionSourceDomain z).subtype)
    (fun value => value.2)

def halfPositionGraphPairFeature (z : ℂ) :
    quarterMellinHalfPositionSourceDomain z →ₗ[ℂ]
      (PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy) :=
  ((quarterMellinL2Feature z).comp
      (quarterMellinHalfPositionSourceDomain z).subtype).prod
    (HalfPositionOperator.toFun.comp (halfPositionDomainFeature z))

theorem halfPositionGraphPairFeature_mem
    (z : ℂ) (value : quarterMellinHalfPositionSourceDomain z) :
    halfPositionGraphPairFeature z value ∈ HalfPositionOperator.graph := by
  change ((quarterMellinL2Feature z) value.1,
      HalfPositionOperator (halfPositionDomainFeature z value)) ∈
    HalfPositionOperator.graph
  exact LinearPMap.mem_graph HalfPositionOperator
    (halfPositionDomainFeature z value)

def halfPositionGraphFeature (z : ℂ) :
    quarterMellinHalfPositionSourceDomain z →ₗ[ℂ] HalfPositionGraphCarrier :=
  halfPositionProductHilbertEquiv.toLinearMap.comp
    (halfPositionGraphPairFeature z)

def halfPositionGraphFunctional (z : ℂ) :
    quarterMellinHalfPositionSourceDomain z →ₗ[ℂ] ℂ :=
  (quarterMellinL2Functional z).comp
    (quarterMellinHalfPositionSourceDomain z).subtype

def halfPositionGraphToProduct :
    HalfPositionGraphCarrier →L[ℂ]
      (PositiveMellinQuarterEnergy × PositiveMellinQuarterEnergy) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ
      PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy
    ).toContinuousLinearMap

def halfPositionGraphFst :
    HalfPositionGraphCarrier →L[ℂ] PositiveMellinQuarterEnergy :=
  (ContinuousLinearMap.fst ℂ
      PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy).comp
    halfPositionGraphToProduct

theorem halfPositionGraphToProduct_feature
    (z : ℂ) (value : quarterMellinHalfPositionSourceDomain z) :
    halfPositionGraphToProduct (halfPositionGraphFeature z value) =
      halfPositionGraphPairFeature z value := by
  change (WithLp.prodContinuousLinearEquiv 2 ℂ
      PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy)
      ((WithLp.prodContinuousLinearEquiv 2 ℂ
        PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy).symm
        (halfPositionGraphPairFeature z value)) = _
  exact (WithLp.prodContinuousLinearEquiv 2 ℂ
    PositiveMellinQuarterEnergy PositiveMellinQuarterEnergy
    ).apply_symm_apply _

/-- Every generated Hilbert feature remains in the actual closed partial
operator graph after forgetting the `WithLp` product norm. -/
theorem halfPositionGraphFeature_mem_operatorGraph
    (z : ℂ) (value : quarterMellinHalfPositionSourceDomain z) :
    halfPositionGraphToProduct (halfPositionGraphFeature z value) ∈
      HalfPositionOperator.graph := by
  rw [halfPositionGraphToProduct_feature]
  exact halfPositionGraphPairFeature_mem z value

def halfPositionGraphSourceMorphism (z : ℂ) :
    GraphSourceMorphism
      (C := quarterMellinHalfPositionSourceDomain z)
      (C' := QuarterMellinL2Test z)
      (H := HalfPositionGraphCarrier)
      (H' := PositiveMellinQuarterEnergy)
      (halfPositionGraphFeature z) (halfPositionGraphFunctional z)
      (quarterMellinL2Feature z) (quarterMellinL2Functional z) where
  sourceMap := (quarterMellinHalfPositionSourceDomain z).subtype
  hilbertMap := halfPositionGraphFst
  feature_commutes := by
    apply LinearMap.ext
    intro value
    change (halfPositionGraphToProduct
      (halfPositionGraphFeature z value)).1 =
        quarterMellinL2Feature z value.1
    rw [halfPositionGraphToProduct_feature]
    rfl
  functional_commutes := rfl

def halfPositionRelationGraphSourceMorphism
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    RelationGraphSourceMorphism
      (C := quarterMellinHalfPositionSourceDomain z)
      (C' := QuarterMellinL2Test z)
      (Rel := SchwartzMap ℝ ℂ)
      (Rel' := SchwartzMap ℝ ℂ)
      (H := HalfPositionGraphCarrier)
      (H' := PositiveMellinQuarterEnergy)
      (halfPositionGraphFeature z) (halfPositionGraphFunctional z)
      (coPoissonQuarterHalfPositionRelation z positive belowHalf)
      (quarterMellinL2Feature z) (quarterMellinL2Functional z)
      (coPoissonQuarterMellinConvergentMap z positive belowHalf) where
  graphMorphism := halfPositionGraphSourceMorphism z
  relationMap := LinearMap.id
  relation_commutes := by
    apply LinearMap.ext
    intro test
    rfl

end
end HalfPositionSource
end MuntzConductor
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
