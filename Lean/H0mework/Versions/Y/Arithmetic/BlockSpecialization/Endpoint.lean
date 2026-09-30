import H0mework.Versions.Y.Arithmetic.BlockSpecialization.WholeComplex
import H0mework.Versions.Y.Arithmetic.EulerAnalytic.EndpointBoundaryEigenAction
import H0mework.Versions.Y.Arithmetic.EulerAnalytic.CoordinateEndpointSection
import H0mework.Versions.Y.Arithmetic.EulerGlobal.HistoryRelationEmbedding

/-!
# Block endpoints at the existing arithmetic whole-relation face

The universal block endpoints specialize directly to the already installed
integral endpoint section.  The block boundary likewise reads as the existing
integral `localEndpointBoundaryRelation`; no second endpoint carrier is
introduced.

At an actual row whose prime is `3`, this specialized boundary has no
preimage under `id - Euler`.  Arithmetic specialization therefore does not
silently kill the endpoint class.
-/

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace BlockArithmeticSpecializationEndpoint

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open CanonicalUnitArithmeticFactorizationWholeHistoryIntegralRelationEmbedding
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection
open BlockArithmeticSpecializationStage
open BlockArithmeticSpecializationWholeComplex

noncomputable section

/-- Coefficientwise arithmetic evaluation of the existing block endpoint
basis into the already installed integral `DualBase`. -/
def blockDualBaseArithmeticRead : BlockDualBase →ₗ[ℤ] DualBase where
  toFun := fun value index => actualBlockSpecialization (value index)
  map_add' := by
    intro left right
    funext index
    exact map_add actualBlockSpecialization _ _
  map_smul' := by
    intro scalar value
    funext index
    simp [actualBlockSpecialization]

theorem localBlockEndpointVertexMap_arithmetic_read
    (stage : Nat) (base : BlockDualBase) :
    blockWholeVertexRead seedOccurrence.root stage
        (localBlockEndpointVertexMap stage base) =
      localEndpointVertexMap stage (blockDualBaseArithmeticRead base) := by
  funext role
  cases role with
  | none => rfl
  | some row => exact (blockInnerCarrierRead seedOccurrence.root stage).map_zero

@[simp] theorem blockDualBaseArithmeticRead_left :
    blockDualBaseArithmeticRead blockLeftEndpointBase = leftEndpointBase := by
  funext index
  fin_cases index <;>
    simp [blockDualBaseArithmeticRead, blockLeftEndpointBase,
      leftEndpointBase]

@[simp] theorem blockDualBaseArithmeticRead_right :
    blockDualBaseArithmeticRead blockRightEndpointBase = rightEndpointBase := by
  funext index
  fin_cases index <;>
    simp [blockDualBaseArithmeticRead, blockRightEndpointBase,
      rightEndpointBase]

theorem localBlockLeftEndpoint_arithmetic_read (stage : Nat) :
    blockWholeVertexRead seedOccurrence.root stage
        (localBlockEndpointVertexMap stage blockLeftEndpointBase) =
      localEndpointVertexMap stage leftEndpointBase := by
  rw [localBlockEndpointVertexMap_arithmetic_read,
    blockDualBaseArithmeticRead_left]

theorem localBlockRightEndpoint_arithmetic_read (stage : Nat) :
    blockWholeVertexRead seedOccurrence.root stage
        (localBlockEndpointVertexMap stage blockRightEndpointBase) =
      localEndpointVertexMap stage rightEndpointBase := by
  rw [localBlockEndpointVertexMap_arithmetic_read,
    blockDualBaseArithmeticRead_right]

/-- The literal block boundary reads back as the existing integral endpoint
boundary, not a newly defined comparison shadow. -/
theorem localBlockEndpointBoundaryRelation_arithmetic_read (stage : Nat) :
    blockWholeRelationRead seedOccurrence.root stage
        (localBlockEndpointBoundaryRelation stage) =
      localEndpointBoundaryRelation stage := by
  rw [←
    CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction.blockFactorizationDifferential_leftEndpoint]
  have square := LinearMap.congr_fun
    (blockFactorizationDifferential_specialization_square
      seedOccurrence.root stage)
    (localBlockEndpointVertexMap stage blockLeftEndpointBase)
  simp only [LinearMap.comp_apply] at square
  rw [localBlockLeftEndpoint_arithmetic_read,
    CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection.factorizationDifferential_leftEndpoint]
    at square
  exact square

theorem localBlockRightBoundary_arithmetic_read (stage : Nat) :
    blockWholeRelationRead seedOccurrence.root stage
        (-localBlockEndpointBoundaryRelation stage) =
      -localEndpointBoundaryRelation stage := by
  rw [←
    CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction.blockFactorizationDifferential_rightEndpoint]
  have square := LinearMap.congr_fun
    (blockFactorizationDifferential_specialization_square
      seedOccurrence.root stage)
    (localBlockEndpointVertexMap stage blockRightEndpointBase)
  simp only [LinearMap.comp_apply] at square
  rw [localBlockRightEndpoint_arithmetic_read,
    CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection.factorizationDifferential_rightEndpoint]
    at square
  exact square

def integralRelationEulerOperator (stage : Nat) :
    WholeRelationModule seedOccurrence.root stage →ₗ[ℤ]
      WholeRelationModule seedOccurrence.root stage :=
  LinearMap.id - relationEulerAction seedOccurrence.root stage

def integralBoundaryCoordinate (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    WholeRelationModule seedOccurrence.root stage →ₗ[ℤ] ℤ where
  toFun := fun value =>
    baseRead seedOccurrence.root stage (value row) (row.1, 0)
  map_add' := by intro left right; simp
  map_smul' := by intro scalar value; simp

theorem integralBoundaryCoordinate_endpoint (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    integralBoundaryCoordinate stage row
        (localEndpointBoundaryRelation stage) = 1 := by
  simp [integralBoundaryCoordinate, localEndpointBoundaryRelation,
    localInnerEmbedding, constantEulerBase, endpointAntiInvariantBase,
    leftEndpointBase, rightEndpointBase,
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.baseRead_solutionOfBase]

theorem baseRead_carrierEulerAction
    (stage : Nat)
    (value : CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.Carrier
      seedOccurrence.root stage)
    (index : BaseIndex seedOccurrence.root stage) :
    baseRead seedOccurrence.root stage
        (carrierEulerAction seedOccurrence.root stage value) index =
      actualPrimeScalar seedOccurrence.root stage index.1 *
        baseRead seedOccurrence.root stage value index := by
  rcases index with ⟨primeIndex, dualIndex⟩
  simp [baseRead, carrierEulerAction,
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.vertexEulerAction,
    exponentZero]

theorem integralBoundaryCoordinate_relationEulerAction
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (value : WholeRelationModule seedOccurrence.root stage) :
    integralBoundaryCoordinate stage row
        (relationEulerAction seedOccurrence.root stage value) =
      actualPrimeScalar seedOccurrence.root stage row.1 *
        integralBoundaryCoordinate stage row value := by
  change baseRead seedOccurrence.root stage
      (carrierEulerAction seedOccurrence.root stage (value row))
        (row.1, 0) =
    actualPrimeScalar seedOccurrence.root stage row.1 *
      baseRead seedOccurrence.root stage (value row) (row.1, 0)
  exact baseRead_carrierEulerAction stage (value row) (row.1, 0)

theorem integralBoundaryCoordinate_operator (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (value : WholeRelationModule seedOccurrence.root stage) :
    integralBoundaryCoordinate stage row
        (integralRelationEulerOperator stage value) =
      (1 - ((rowPrime row : Nat) : ℤ)) *
        integralBoundaryCoordinate stage row value := by
  unfold integralRelationEulerOperator
  rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub,
    integralBoundaryCoordinate_relationEulerAction]
  have primeEq : ((rowPrime row : Nat) : ℤ) =
      actualPrimeScalar seedOccurrence.root stage row.1 := rfl
  rw [primeEq]
  ring

/-- Direct prime-three guard: at an actual `p = 3` row the existing integral
endpoint boundary has no preimage under `id - Euler`. -/
theorem localEndpointBoundary_not_operator_range_at_three
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (primeThree : (rowPrime row : Nat) = 3) :
    ¬ ∃ preimage : WholeRelationModule seedOccurrence.root stage,
      localEndpointBoundaryRelation stage =
        integralRelationEulerOperator stage preimage := by
  rintro ⟨preimage, equality⟩
  have mapped := congrArg (integralBoundaryCoordinate stage row) equality
  rw [integralBoundaryCoordinate_endpoint,
    integralBoundaryCoordinate_operator] at mapped
  have primeThreeInt : ((rowPrime row : Nat) : ℤ) = 3 := by
    exact_mod_cast primeThree
  rw [primeThreeInt] at mapped
  omega

end
end BlockArithmeticSpecializationEndpoint
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
