import H0mework.Versions.Y.Arithmetic.EulerAnalytic.TautologicalReadback

/-!
# Actual anti-eigen action on the analytic endpoint boundary

The source-owned endpoint differential is retained as the literal
anti-invariant whole-relation row.  In the common prime-dual block frame the
Euler action on that row has eigenvalue `A_p - B_p`, whose installed analytic
readout is the second prime eigenvalue.  Thus `1-M` does not kill the endpoint
difference by definition; any later mapped-boundary descent must supply its
actual preimage.

No inverse, zero, fixedness, endpoint equality, or action-zero premise enters
this calculation.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticGlobalActionCofiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate
open CategoryTheory
open scoped ChangeOfRings

noncomputable section

def blockAntiEigenvalue (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage) :
    BlockCoordinateRing :=
  blockA ((stageFactorization seedOccurrence.root stage).actualPrime primeIndex) -
    blockB ((stageFactorization seedOccurrence.root stage).actualPrime primeIndex)

/-- The actual endpoint boundary lies pointwise in the nontrivial
anti-invariant eigenline. -/
theorem blockInnerAction_localBlockEndpointAntiInvariant
    (stage : Nat) (index : BaseIndex seedOccurrence.root stage) :
    blockInnerAction seedOccurrence.root stage
        (localBlockEndpointAntiInvariant stage) index =
      blockAntiEigenvalue stage index.1 *
        localBlockEndpointAntiInvariant stage index := by
  rcases index with ⟨primeIndex, dualIndex⟩
  fin_cases dualIndex <;>
    simp [blockInnerAction, blockAntiEigenvalue,
      localBlockEndpointAntiInvariant,
      blockWholeAntiInvariantProjection,
      blockInnerAntiInvariant, blockInnerReversal,
      localBlockEndpointVertexMap, blockLeftEndpointBase] <;>
    ring

/-- The installed anti-eigenvalue is the second pair coordinate's genuine
local Euler eigenvalue, not zero. -/
theorem blockCoordinateToPairZeroFiber_antiEigenvalue
    (stage : Nat) (primeIndex : StagePrime seedOccurrence.root stage) :
    blockCoordinateToPairZeroFiber
        (blockAntiEigenvalue stage primeIndex) =
      pairFunctionToZeroFiber
        (fun pair => installedPrimeEigenvalue
          ((stageFactorization seedOccurrence.root stage).actualPrime primeIndex)
          pair.2) := by
  unfold blockAntiEigenvalue
  exact blockCoordinateToPairZeroFiber_A_sub_B _

def pairBlockLocalEulerAction (stage : Nat) :
    PairBlockLocalState stage ⟶ PairBlockLocalState stage :=
  PairBlockExtensionFunctor.map
    (blockDirectEulerAction seedOccurrence.root stage)

def pairBlockLocalEulerOperator (stage : Nat) :
    PairBlockLocalState stage ⟶ PairBlockLocalState stage :=
  𝟙 _ - pairBlockLocalEulerAction stage

def localPairEndpointBoundary (stage : Nat) :
    (PairBlockLocalState stage).X 1 :=
  ((PairBlockLocalState stage).d 0 1).hom
    (pairBlockLocalEndpointSection stage)

def localBlockEndpointBoundaryRelation (stage : Nat) :
    BlockWholeRelation seedOccurrence.root stage :=
  fun _row => localBlockEndpointAntiInvariant stage

theorem blockFactorizationDifferential_leftEndpoint (stage : Nat) :
    blockFactorizationDifferential seedOccurrence.root stage
        (localBlockEndpointVertexMap stage blockLeftEndpointBase) =
      localBlockEndpointBoundaryRelation stage := by
  funext row index
  rcases index with ⟨primeIndex, dualIndex⟩
  fin_cases dualIndex <;>
    simp [blockFactorizationDifferential,
      localBlockEndpointVertexMap, blockLeftEndpointBase,
      localBlockEndpointBoundaryRelation,
      localBlockEndpointAntiInvariant,
      blockWholeAntiInvariantProjection,
      blockInnerAntiInvariant, blockInnerReversal]

theorem blockFactorizationDifferential_rightEndpoint (stage : Nat) :
    blockFactorizationDifferential seedOccurrence.root stage
        (localBlockEndpointVertexMap stage blockRightEndpointBase) =
      -localBlockEndpointBoundaryRelation stage := by
  funext row index
  rcases index with ⟨primeIndex, dualIndex⟩
  fin_cases dualIndex <;>
    simp [blockFactorizationDifferential,
      localBlockEndpointVertexMap, blockRightEndpointBase,
      localBlockEndpointBoundaryRelation,
      localBlockEndpointAntiInvariant,
      blockWholeAntiInvariantProjection,
      blockInnerAntiInvariant, blockInnerReversal,
      blockLeftEndpointBase]

def localPairEndpointBoundaryActual (stage : Nat) :
    (PairBlockLocalState stage).X 1 :=
  (universalLeftCoordinate installedOwner -
      universalRightCoordinate installedOwner)
    ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
      localBlockEndpointBoundaryRelation stage

theorem localPairEndpointBoundary_eq_actual (stage : Nat) :
    localPairEndpointBoundary stage =
      localPairEndpointBoundaryActual stage := by
  letI : Module BlockCoordinateRing PairCoefficientRing :=
    Module.compHom PairCoefficientRing blockCoordinateToPairZeroFiber
  have leftApply :
      (ModuleCat.ofHom
          (blockFactorizationDifferential seedOccurrence.root stage)).hom
          (localBlockEndpointVertexMap stage blockLeftEndpointBase) =
        localBlockEndpointBoundaryRelation stage :=
    by simpa using blockFactorizationDifferential_leftEndpoint stage
  have rightApply :
      (ModuleCat.ofHom
          (blockFactorizationDifferential seedOccurrence.root stage)).hom
          (localBlockEndpointVertexMap stage blockRightEndpointBase) =
        -localBlockEndpointBoundaryRelation stage :=
    by simpa using blockFactorizationDifferential_rightEndpoint stage
  change
    (ModuleCat.extendScalars blockCoordinateToPairZeroFiber).map
        (ModuleCat.ofHom
          (blockFactorizationDifferential seedOccurrence.root stage))
        (pairBlockLocalEndpointSection stage) = _
  rw [pairBlockLocalEndpointSection, map_add,
    ModuleCat.ExtendScalars.map_tmul,
    ModuleCat.ExtendScalars.map_tmul,
    leftApply, rightApply,
    TensorProduct.tmul_neg, ← TensorProduct.neg_tmul,
    ← TensorProduct.add_tmul]
  rfl

def localBlockEndpointWeightedBoundary (stage : Nat) :
    BlockWholeRelation seedOccurrence.root stage :=
  fun row index =>
    blockAntiEigenvalue stage index.1 *
      localBlockEndpointBoundaryRelation stage row index

theorem blockWholeRelationAction_endpointBoundary (stage : Nat) :
    blockWholeRelationAction seedOccurrence.root stage
        (localBlockEndpointBoundaryRelation stage) =
      localBlockEndpointWeightedBoundary stage := by
  funext row index
  exact blockInnerAction_localBlockEndpointAntiInvariant stage index

def localPairEndpointWeightedBoundary (stage : Nat) :
    (PairBlockLocalState stage).X 1 :=
  (universalLeftCoordinate installedOwner -
      universalRightCoordinate installedOwner)
    ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
      localBlockEndpointWeightedBoundary stage

theorem pairBlockLocalEulerAction_boundary_eq_weighted (stage : Nat) :
    ((pairBlockLocalEulerAction stage).f 1).hom
        (localPairEndpointBoundary stage) =
      localPairEndpointWeightedBoundary stage := by
  letI : Module BlockCoordinateRing PairCoefficientRing :=
    Module.compHom PairCoefficientRing blockCoordinateToPairZeroFiber
  have actionApply :
      (ModuleCat.ofHom
          (blockWholeRelationAction seedOccurrence.root stage)).hom
          (localBlockEndpointBoundaryRelation stage) =
        localBlockEndpointWeightedBoundary stage :=
    by simpa using blockWholeRelationAction_endpointBoundary stage
  rw [localPairEndpointBoundary_eq_actual]
  change
    (ModuleCat.extendScalars blockCoordinateToPairZeroFiber).map
        (ModuleCat.ofHom
          (blockWholeRelationAction seedOccurrence.root stage))
        ((universalLeftCoordinate installedOwner -
            universalRightCoordinate installedOwner)
          ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
            localBlockEndpointBoundaryRelation stage) = _
  rw [ModuleCat.ExtendScalars.map_tmul, actionApply]
  rfl

theorem pairBlockLocalEulerOperator_boundary_eq_actual_sub_weighted
    (stage : Nat) :
    ((pairBlockLocalEulerOperator stage).f 1).hom
        (localPairEndpointBoundary stage) =
      localPairEndpointBoundaryActual stage -
        localPairEndpointWeightedBoundary stage := by
  calc
    _ = localPairEndpointBoundary stage -
          ((pairBlockLocalEulerAction stage).f 1).hom
            (localPairEndpointBoundary stage) := by
      simp [pairBlockLocalEulerOperator]
    _ = _ := by
      rw [pairBlockLocalEulerAction_boundary_eq_weighted,
        localPairEndpointBoundary_eq_actual]

def endpointBoundaryEigenOccurrence (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload ×
        ((PairBlockLocalState stage).X 1 ×
          (PairBlockLocalState stage).X 1)) :=
  seedOccurrence.map fun owner =>
    (owner, (localPairEndpointBoundaryActual stage,
      localPairEndpointWeightedBoundary stage))

theorem endpointBoundaryEigenOccurrence_projects (stage : Nat) :
    (endpointBoundaryEigenOccurrence stage).map Prod.fst = seedOccurrence := by
  unfold endpointBoundaryEigenOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_actual_endpoint_boundary_and_nontrivial_anti_eigen_action
    (stage : Nat) :
    (endpointBoundaryEigenOccurrence stage).map Prod.fst = seedOccurrence ∧
      localPairEndpointBoundary stage =
        localPairEndpointBoundaryActual stage ∧
      ((pairBlockLocalEulerAction stage).f 1).hom
          (localPairEndpointBoundary stage) =
        localPairEndpointWeightedBoundary stage ∧
      ((pairBlockLocalEulerOperator stage).f 1).hom
          (localPairEndpointBoundary stage) =
        localPairEndpointBoundaryActual stage -
          localPairEndpointWeightedBoundary stage := by
  exact ⟨endpointBoundaryEigenOccurrence_projects stage,
    localPairEndpointBoundary_eq_actual stage,
    pairBlockLocalEulerAction_boundary_eq_weighted stage,
    pairBlockLocalEulerOperator_boundary_eq_actual_sub_weighted stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
