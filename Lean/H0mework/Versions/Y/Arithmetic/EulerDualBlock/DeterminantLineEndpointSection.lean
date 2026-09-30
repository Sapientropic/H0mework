import H0mework.Versions.Y.Arithmetic.EulerAnalytic.CoordinateEndpointSection
import H0mework.Versions.Y.Arithmetic.EulerDualBlock.DeterminantLineCoordinate

/-!
# Actual endpoint section over the prime-dual determinant-line zero fibre

The installed pair zero fibre supplies its two universal coordinates.  The
same source-generated whole relation family supplies the persistent left and
right endpoints, their actual swap, and the factorization differential.  The
result is one fixedness-free two-term chain over the direct block determinant
line owner.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineEndpointSection

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolution
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate
open scoped TensorProduct

noncomputable section

abbrev PairCoefficientRing := AnalyticZeroFiberRing installedOwner

abbrev PairScalarVertex :=
  TensorProduct ℤ PairCoefficientRing GlobalVertex

abbrev PairScalarRelation :=
  TensorProduct ℤ PairCoefficientRing GlobalRelation

def pairExtendedDifferential :
    PairScalarVertex →ₗ[ℤ] PairScalarRelation :=
  TensorProduct.map LinearMap.id globalDifferential

def pairExtendedReversal :
    PairScalarVertex →ₗ[ℤ] PairScalarVertex :=
  TensorProduct.map LinearMap.id globalReversalZero

def universalPairEndpointSection : PairScalarVertex :=
  universalLeftCoordinate installedOwner ⊗ₜ[ℤ] actualGlobalLeftEndpoint +
    universalRightCoordinate installedOwner ⊗ₜ[ℤ] actualGlobalRightEndpoint

theorem pairExtendedReversal_universalEndpointSection :
    pairExtendedReversal universalPairEndpointSection =
      universalLeftCoordinate installedOwner ⊗ₜ[ℤ]
          actualGlobalRightEndpoint +
        universalRightCoordinate installedOwner ⊗ₜ[ℤ]
          actualGlobalLeftEndpoint := by
  simp only [pairExtendedReversal, universalPairEndpointSection, map_add,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rw [actualGlobalReversalZero_leftEndpoint,
    actualGlobalReversalZero_rightEndpoint]

abbrev PairPoint := Point installedOwner

def pairPointCoefficientMap (point : PairPoint) :
    PairCoefficientRing →ₗ[ℤ] ℂ :=
  point.specialization.toAddMonoidHom.toIntLinearMap

abbrev PairComplexScalarVertex := TensorProduct ℤ ℂ GlobalVertex

def pairPointVertexSpecialization (point : PairPoint) :
    PairScalarVertex →ₗ[ℤ] PairComplexScalarVertex :=
  TensorProduct.map (pairPointCoefficientMap point) LinearMap.id

theorem pairPointVertexSpecialization_universalEndpointSection
    (point : PairPoint) :
    pairPointVertexSpecialization point universalPairEndpointSection =
      point.pair.1 ⊗ₜ[ℤ] actualGlobalLeftEndpoint +
        point.pair.2 ⊗ₜ[ℤ] actualGlobalRightEndpoint := by
  simp [pairPointVertexSpecialization, universalPairEndpointSection,
    pairPointCoefficientMap]

theorem mathlibPointVertexSpecialization_universalEndpointSection
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0) :
    pairPointVertexSpecialization
        (pointOfMathlibZero coordinate zetaZero)
        universalPairEndpointSection =
      coordinate ⊗ₜ[ℤ] actualGlobalLeftEndpoint +
        coordinateReversal coordinate ⊗ₜ[ℤ]
          actualGlobalRightEndpoint := by
  rw [pairPointVertexSpecialization_universalEndpointSection]
  rfl

def pairComplexWholeEndpointRead (dualIndex : Fin 2) :
    PairComplexScalarVertex →ₗ[ℤ] ℂ :=
  (TensorProduct.rid ℤ ℂ).toLinearMap.comp
    (TensorProduct.map LinearMap.id
      (actualGlobalWholeEndpointRead dualIndex))

@[simp] theorem pairComplexWholeEndpointRead_tmul
    (dualIndex : Fin 2) (coefficient : ℂ) (vertex : GlobalVertex) :
    pairComplexWholeEndpointRead dualIndex
        (coefficient ⊗ₜ[ℤ] vertex) =
      coefficient * actualGlobalWholeEndpointRead dualIndex vertex := by
  simp [pairComplexWholeEndpointRead, mul_comm]

theorem pairPointSpecialization_leftEndpoint (point : PairPoint) :
    pairComplexWholeEndpointRead 0
        (pairPointVertexSpecialization point universalPairEndpointSection) =
      point.pair.1 := by
  rw [pairPointVertexSpecialization_universalEndpointSection, map_add]
  simp

theorem pairPointSpecialization_rightEndpoint (point : PairPoint) :
    pairComplexWholeEndpointRead 1
        (pairPointVertexSpecialization point universalPairEndpointSection) =
      point.pair.2 := by
  rw [pairPointVertexSpecialization_universalEndpointSection, map_add]
  simp

/-! ## The actual local two-term differential -/

abbrev PairLocalWholeVertex (stage : Nat) :=
  TensorProduct ℤ PairCoefficientRing
    (WholeVertexModule seedOccurrence.root stage)

abbrev PairLocalWholeRelation (stage : Nat) :=
  TensorProduct ℤ PairCoefficientRing
    (WholeRelationModule seedOccurrence.root stage)

def localUniversalPairEndpointSection (stage : Nat) :
    PairLocalWholeVertex stage :=
  universalLeftCoordinate installedOwner ⊗ₜ[ℤ]
      localEndpointVertexMap stage leftEndpointBase +
    universalRightCoordinate installedOwner ⊗ₜ[ℤ]
      localEndpointVertexMap stage rightEndpointBase

def localPairFactorizationDifferential (stage : Nat) :
    PairLocalWholeVertex stage →ₗ[ℤ] PairLocalWholeRelation stage :=
  TensorProduct.map LinearMap.id
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.factorizationDifferential
      seedOccurrence.root stage)

theorem localPairEndpoint_differential (stage : Nat) :
    localPairFactorizationDifferential stage
        (localUniversalPairEndpointSection stage) =
      (universalLeftCoordinate installedOwner -
          universalRightCoordinate installedOwner) ⊗ₜ[ℤ]
        localEndpointBoundaryRelation stage := by
  simp only [localPairFactorizationDifferential,
    localUniversalPairEndpointSection, map_add,
    TensorProduct.map_tmul, LinearMap.id_apply,
    factorizationDifferential_leftEndpoint,
    factorizationDifferential_rightEndpoint,
    TensorProduct.tmul_neg]
  rw [sub_eq_add_neg, TensorProduct.add_tmul, TensorProduct.neg_tmul]

def pairEndpointSectionOccurrence : RootedAccountedUnfolding
    (FactorizationPayload × PairScalarVertex) :=
  seedOccurrence.map fun owner => (owner, universalPairEndpointSection)

theorem pairEndpointSectionOccurrence_projects :
    pairEndpointSectionOccurrence.map Prod.fst = seedOccurrence := by
  unfold pairEndpointSectionOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_same_owner_pair_zero_fibre_endpoints_and_actual_boundary
    (stage : Nat) (point : PairPoint) :
    pairEndpointSectionOccurrence.map Prod.fst = seedOccurrence ∧
      pairPointVertexSpecialization point universalPairEndpointSection =
        point.pair.1 ⊗ₜ[ℤ] actualGlobalLeftEndpoint +
          point.pair.2 ⊗ₜ[ℤ] actualGlobalRightEndpoint ∧
      localPairFactorizationDifferential stage
          (localUniversalPairEndpointSection stage) =
        (universalLeftCoordinate installedOwner -
            universalRightCoordinate installedOwner) ⊗ₜ[ℤ]
          localEndpointBoundaryRelation stage := by
  exact ⟨pairEndpointSectionOccurrence_projects,
    pairPointVertexSpecialization_universalEndpointSection point,
    localPairEndpoint_differential stage⟩

end
end CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineEndpointSection
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
