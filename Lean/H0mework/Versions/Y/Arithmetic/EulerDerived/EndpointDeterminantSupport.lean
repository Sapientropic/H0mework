import H0mework.Versions.Y.Arithmetic.EulerAnalytic.EndpointBoundaryEigenAction

/-!
# Determinant support of the actual endpoint boundary

For every finite source stage, the anti-eigen cofactor of the canonical block
determinant gives an explicit preimage of the determinant-scaled endpoint
boundary under `1-M` on the whole relation carrier.  Consequently the actual
relation-action cokernel class is annihilated by the same determinant section
generated from the whole complex.

This is the source-native adjugate calculation.  It neither inverts a local
Euler factor nor identifies the scaled class with the unscaled endpoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDeterminantSupport

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection

noncomputable section

def blockInvariantEigenvalue (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage) :
    BlockCoordinateRing :=
  blockA ((stageFactorization seedOccurrence.root stage).actualPrime primeIndex) +
    blockB ((stageFactorization seedOccurrence.root stage).actualPrime primeIndex)

def blockAntiOperatorFactor (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage) :
    BlockCoordinateRing :=
  1 - blockAntiEigenvalue stage primeIndex

def blockInvariantOperatorFactor (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage) :
    BlockCoordinateRing :=
  1 - blockInvariantEigenvalue stage primeIndex

def blockLocalDeterminantFactor (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage) :
    BlockCoordinateRing :=
  (1 - blockA
      ((stageFactorization seedOccurrence.root stage).actualPrime primeIndex)) ^ 2 -
    blockB
      ((stageFactorization seedOccurrence.root stage).actualPrime primeIndex) ^ 2

theorem blockLocalDeterminantFactor_eq_eigenProduct
    (stage : Nat) (primeIndex : StagePrime seedOccurrence.root stage) :
    blockLocalDeterminantFactor stage primeIndex =
      blockAntiOperatorFactor stage primeIndex *
        blockInvariantOperatorFactor stage primeIndex := by
  unfold blockLocalDeterminantFactor blockAntiOperatorFactor
    blockInvariantOperatorFactor blockAntiEigenvalue
    blockInvariantEigenvalue
  ring

/-- The anti-eigen entry of the canonical block adjugate, written without
division. -/
def blockAntiAdjugateCofactor (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage) :
    BlockCoordinateRing :=
  blockInvariantOperatorFactor stage primeIndex *
    (Finset.univ.erase primeIndex).prod
      (blockLocalDeterminantFactor stage)

theorem blockAntiOperatorFactor_mul_adjugateCofactor
    (stage : Nat) (primeIndex : StagePrime seedOccurrence.root stage) :
    blockAntiOperatorFactor stage primeIndex *
        blockAntiAdjugateCofactor stage primeIndex =
      blockDeterminantSection seedOccurrence.root stage := by
  rw [blockDeterminantSection_eq_actual_product]
  change _ = ∏ otherIndex : StagePrime seedOccurrence.root stage,
    blockLocalDeterminantFactor stage otherIndex
  unfold blockAntiAdjugateCofactor
  rw [← mul_assoc]
  rw [← blockLocalDeterminantFactor_eq_eigenProduct]
  simpa using Finset.mul_prod_erase (Finset.univ)
    (blockLocalDeterminantFactor stage) (Finset.mem_univ primeIndex)

def blockEndpointBoundaryDeterminantPreimage (stage : Nat) :
    BlockWholeRelation seedOccurrence.root stage :=
  fun row index =>
    blockAntiAdjugateCofactor stage index.1 *
      localBlockEndpointBoundaryRelation stage row index

/-- Canonical cofactor calculation: the whole determinant multiple of the
endpoint boundary is in the actual `1-M` range. -/
theorem blockWholeRelationEulerOperator_adjugate_preimage (stage : Nat) :
    blockWholeRelationEulerOperator seedOccurrence.root stage
        (blockEndpointBoundaryDeterminantPreimage stage) =
      blockDeterminantSection seedOccurrence.root stage •
        localBlockEndpointBoundaryRelation stage := by
  funext row index
  rcases index with ⟨primeIndex, dualIndex⟩
  have factor := blockAntiOperatorFactor_mul_adjugateCofactor
    stage primeIndex
  fin_cases dualIndex <;>
    simp [blockWholeRelationEulerOperator, blockWholeRelationAction,
      blockInnerAction, blockEndpointBoundaryDeterminantPreimage,
      localBlockEndpointBoundaryRelation,
      localBlockEndpointAntiInvariant,
      blockWholeAntiInvariantProjection, blockInnerAntiInvariant,
      blockInnerReversal, localBlockEndpointVertexMap,
      blockLeftEndpointBase] <;>
    rw [← factor] <;>
    unfold blockAntiOperatorFactor blockAntiEigenvalue <;>
    ring

abbrev LocalRelationActionCokernel (stage : Nat) :=
  (BlockWholeRelation seedOccurrence.root stage) ⧸
    LinearMap.range
      (blockWholeRelationEulerOperator seedOccurrence.root stage)

def localRelationActionCokernelProjection (stage : Nat) :
    BlockWholeRelation seedOccurrence.root stage →ₗ[BlockCoordinateRing]
      LocalRelationActionCokernel stage :=
  Submodule.mkQ _

theorem determinant_smul_endpointBoundary_mem_operatorRange (stage : Nat) :
    blockDeterminantSection seedOccurrence.root stage •
        localBlockEndpointBoundaryRelation stage ∈
      LinearMap.range
        (blockWholeRelationEulerOperator seedOccurrence.root stage) := by
  refine ⟨blockEndpointBoundaryDeterminantPreimage stage, ?_⟩
  exact blockWholeRelationEulerOperator_adjugate_preimage stage

theorem determinant_smul_endpointBoundary_zero_in_cokernel (stage : Nat) :
    localRelationActionCokernelProjection stage
        (blockDeterminantSection seedOccurrence.root stage •
          localBlockEndpointBoundaryRelation stage) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact determinant_smul_endpointBoundary_mem_operatorRange stage

def endpointBoundaryDeterminantSupportOccurrence (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload ×
        (BlockWholeRelation seedOccurrence.root stage ×
          BlockWholeRelation seedOccurrence.root stage)) :=
  seedOccurrence.map fun owner =>
    (owner, (localBlockEndpointBoundaryRelation stage,
      blockEndpointBoundaryDeterminantPreimage stage))

theorem endpointBoundaryDeterminantSupportOccurrence_projects (stage : Nat) :
    (endpointBoundaryDeterminantSupportOccurrence stage).map Prod.fst =
      seedOccurrence := by
  unfold endpointBoundaryDeterminantSupportOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_exact_endpoint_boundary_whole_determinant_and_cokernel_support
    (stage : Nat) :
    (endpointBoundaryDeterminantSupportOccurrence stage).map Prod.fst =
        seedOccurrence ∧
      blockWholeRelationEulerOperator seedOccurrence.root stage
          (blockEndpointBoundaryDeterminantPreimage stage) =
        blockDeterminantSection seedOccurrence.root stage •
          localBlockEndpointBoundaryRelation stage ∧
      localRelationActionCokernelProjection stage
          (blockDeterminantSection seedOccurrence.root stage •
            localBlockEndpointBoundaryRelation stage) = 0 := by
  exact ⟨endpointBoundaryDeterminantSupportOccurrence_projects stage,
    blockWholeRelationEulerOperator_adjugate_preimage stage,
    determinant_smul_endpointBoundary_zero_in_cokernel stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDeterminantSupport
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
