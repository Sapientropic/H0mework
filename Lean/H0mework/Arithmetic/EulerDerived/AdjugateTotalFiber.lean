import H0mework.Realization.MappingCone.AdjugateTotalFiber
import H0mework.Arithmetic.EulerDerived.ComplexAdjugate

/-!
# Actual whole-complex adjugate total fibre

The common prime-dual whole complex instantiates the generic determinant-
adjugate total-fibre closure.  The domain supplies only its already proved
whole-complex identity `Q ≫ T = D`; the generic mapping-cocone lift generates
the total-fibre map.  Its second source coordinate reads every endpoint back
literally, while the same chain map also carries the endpoint differential.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber

open CategoryTheory
open CategoryTheory.Limits
open CochainMappingCoconeDeterminantAdjugateInclusion
open CochainMappingCoconeDeterminantAdjugateTotalFiber
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugate
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant

noncomputable section

abbrev LocalWholeComplex (stage : Nat) :=
  blockDirectComplex seedOccurrence.root stage

theorem localAdjugateSquare (stage : Nat) :
    ActionDeterminantAdjugateAt
      (blockDirectEulerOperator stage)
      (blockDirectDeterminantMultiplication stage)
      (blockDirectAdjugate stage) :=
  ⟨blockDirectEulerOperator_comp_adjugate stage⟩

noncomputable abbrev LocalTotalFiber (stage : Nat) :=
  TotalFiber (blockDirectEulerOperator stage)
    (blockDirectDeterminantMultiplication stage)

noncomputable def localTotalInclusion (stage : Nat) :
    LocalWholeComplex stage ⟶ LocalTotalFiber stage :=
  totalInclusion (localAdjugateSquare stage)

theorem localTotalInclusion_fst (stage : Nat) :
    localTotalInclusion stage ≫
        CochainComplex.mappingCocone.fst
          (totalRow (blockDirectEulerOperator stage)
            (blockDirectDeterminantMultiplication stage)) =
      totalKernelPair (blockDirectAdjugate stage) :=
  totalInclusion_fst (localAdjugateSquare stage)

theorem localTotalInclusion_endpoint_readback (stage : Nat) :
    localTotalInclusion stage ≫
        CochainComplex.mappingCocone.fst
          (totalRow (blockDirectEulerOperator stage)
            (blockDirectDeterminantMultiplication stage)) ≫
        (biprod.snd : LocalWholeComplex stage ⊞ LocalWholeComplex stage ⟶
          LocalWholeComplex stage) =
      𝟙 (LocalWholeComplex stage) :=
  totalInclusion_endpoint_readback (localAdjugateSquare stage)

def localTotalEndpointElement
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    (LocalTotalFiber stage).X 0 :=
  (localTotalInclusion stage).f 0 endpoint

def localTotalEndpointReadback
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    (LocalWholeComplex stage).X 0 :=
  ((biprod.snd : LocalWholeComplex stage ⊞ LocalWholeComplex stage ⟶
      LocalWholeComplex stage).f 0).hom
    (((CochainComplex.mappingCocone.fst
      (totalRow (blockDirectEulerOperator stage)
        (blockDirectDeterminantMultiplication stage))).f 0).hom
      (localTotalEndpointElement stage endpoint))

theorem localTotalEndpointReadback_eq
    (stage : Nat) (endpoint : (LocalWholeComplex stage).X 0) :
    localTotalEndpointReadback stage endpoint = endpoint := by
  exact ConcreteCategory.congr_hom
    (totalInclusion_endpoint_readback_f (localAdjugateSquare stage) 0)
    endpoint

def localTotalLeftEndpoint (stage : Nat) : (LocalTotalFiber stage).X 0 :=
  localTotalEndpointElement stage
    (localBlockEndpointVertexMap stage blockLeftEndpointBase)

def localTotalRightEndpoint (stage : Nat) : (LocalTotalFiber stage).X 0 :=
  localTotalEndpointElement stage
    (localBlockEndpointVertexMap stage blockRightEndpointBase)

@[simp] theorem localTotalLeftEndpoint_readback (stage : Nat) :
    localTotalEndpointReadback stage
        (localBlockEndpointVertexMap stage blockLeftEndpointBase) =
      localBlockEndpointVertexMap stage blockLeftEndpointBase :=
  localTotalEndpointReadback_eq stage _

@[simp] theorem localTotalRightEndpoint_readback (stage : Nat) :
    localTotalEndpointReadback stage
        (localBlockEndpointVertexMap stage blockRightEndpointBase) =
      localBlockEndpointVertexMap stage blockRightEndpointBase :=
  localTotalEndpointReadback_eq stage _

def localTotalInclusionOccurrence (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload ×
        (LocalWholeComplex stage ⟶ LocalTotalFiber stage)) :=
  (blockWholeComplexAdjugateOccurrence stage).map fun payload ↦
    (payload.1, localTotalInclusion stage)

theorem localTotalInclusionOccurrence_projects (stage : Nat) :
    (localTotalInclusionOccurrence stage).map Prod.fst =
      stageOccurrenceFrom seedOccurrence.root stage := by
  rw [← blockWholeComplexAdjugateOccurrence_projects_source stage]
  unfold localTotalInclusionOccurrence
  rw [RootedAccountedUnfolding.map_map]
  rfl

theorem preserves_exact_whole_total_fibre_and_endpoint
    (stage : Nat) :
    (localTotalInclusionOccurrence stage).map Prod.fst =
        stageOccurrenceFrom seedOccurrence.root stage ∧
      localTotalInclusion stage ≫
          CochainComplex.mappingCocone.fst
            (totalRow (blockDirectEulerOperator stage)
              (blockDirectDeterminantMultiplication stage)) =
        totalKernelPair (blockDirectAdjugate stage) ∧
      (∀ endpoint : (LocalWholeComplex stage).X 0,
        localTotalEndpointReadback stage endpoint = endpoint) := by
  exact ⟨localTotalInclusionOccurrence_projects stage,
    localTotalInclusion_fst stage,
    localTotalEndpointReadback_eq stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
