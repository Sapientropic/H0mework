import H0mework.Versions.Y.Arithmetic.EulerAnalytic.EndpointBoundaryEigenAction
import H0mework.Arithmetic.CoPoisson.ThetaRoles

/-!
# Raw block relation as an integral scale effect

The universal block coordinate `A_p` is read as the actual integral scale
basis event `delta p`, while `B_p` has zero integral charge.  Coordinate
evaluation on an entire relation carrier then intertwines the block action
with literal left translation.  Consequently the endpoint boundary reads
`delta 1`, and its unquotiented Euler effect reads `delta 1 - delta p`.

No action cokernel, analytic point, zero, inverse or fixedness premise enters
this dependent face.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace ActionCofiber
namespace RawEffect

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter
open ClozelGeneralizedDual.ThetaJRoleRepresentation

noncomputable section

/-- The actual positive scale carried by one generated prime. -/
def blockPrimeScaleUnit (prime : Nat.Primes) : Units NNReal :=
  positiveRealUnit (prime : ℝ) (by exact_mod_cast prime.property.pos)

/-- Universal block coordinates exposed in the integral group ring. -/
def blockCoordinateToIntegralScale :
    BlockCoordinateRing →+* IntegralScaleCarrier :=
  MvPolynomial.eval₂Hom (Int.castRingHom IntegralScaleCarrier) fun index =>
    if index.2 = 0 then delta (blockPrimeScaleUnit index.1) else 0

@[simp] theorem blockCoordinateToIntegralScale_A (prime : Nat.Primes) :
    blockCoordinateToIntegralScale (blockA prime) =
      delta (blockPrimeScaleUnit prime) := by
  simp [blockCoordinateToIntegralScale, blockA]

@[simp] theorem blockCoordinateToIntegralScale_B (prime : Nat.Primes) :
    blockCoordinateToIntegralScale (blockB prime) = 0 := by
  simp [blockCoordinateToIntegralScale, blockB]

/-- One actual row/prime/selected-dual coordinate, evaluated on the whole
relation carrier rather than only on the endpoint. -/
def blockRelationIntegralCoordinate
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    BlockWholeRelation seedOccurrence.root stage →ₛₗ[
      blockCoordinateToIntegralScale] IntegralScaleCarrier where
  toFun relation := blockCoordinateToIntegralScale (relation row (row.1, 0))
  map_add' left right := by
    exact map_add blockCoordinateToIntegralScale _ _
  map_smul' coefficient relation := by
    change blockCoordinateToIntegralScale
        (coefficient * relation row (row.1, 0)) =
      blockCoordinateToIntegralScale coefficient *
        blockCoordinateToIntegralScale (relation row (row.1, 0))
    exact map_mul blockCoordinateToIntegralScale _ _

/-- The full raw action square: multiplication by `A_p` becomes actual
left translation by the corresponding prime event, and the `B_p` channel
has zero integral charge. -/
theorem blockRelationIntegralCoordinate_action
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (relation : BlockWholeRelation seedOccurrence.root stage) :
    blockRelationIntegralCoordinate stage row
        (blockWholeRelationAction seedOccurrence.root stage relation) =
      leftTranslation (blockPrimeScaleUnit (rowPrime row))
        (blockRelationIntegralCoordinate stage row relation) := by
  change blockCoordinateToIntegralScale
      (blockA (rowPrime row) * relation row (row.1, 0) +
        blockB (rowPrime row) * relation row (row.1, 1)) = _
  rw [map_add, map_mul, map_mul,
    blockCoordinateToIntegralScale_A,
    blockCoordinateToIntegralScale_B, zero_mul, add_zero]
  change delta (blockPrimeScaleUnit (rowPrime row)) *
      blockCoordinateToIntegralScale (relation row (row.1, 0)) = _
  rfl

theorem blockRelationIntegralCoordinate_operator
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (relation : BlockWholeRelation seedOccurrence.root stage) :
    blockRelationIntegralCoordinate stage row
        (blockWholeRelationEulerOperator seedOccurrence.root stage relation) =
      blockRelationIntegralCoordinate stage row relation -
        leftTranslation (blockPrimeScaleUnit (rowPrime row))
          (blockRelationIntegralCoordinate stage row relation) := by
  rw [show blockWholeRelationEulerOperator seedOccurrence.root stage relation =
      relation - blockWholeRelationAction seedOccurrence.root stage relation by rfl,
    map_sub, blockRelationIntegralCoordinate_action]

@[simp] theorem blockRelationIntegralCoordinate_endpoint
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    blockRelationIntegralCoordinate stage row
        (localBlockEndpointBoundaryRelation stage) =
      delta (1 : Units NNReal) := by
  simp [blockRelationIntegralCoordinate,
    localBlockEndpointBoundaryRelation,
    localBlockEndpointAntiInvariant,
    blockWholeAntiInvariantProjection, blockInnerAntiInvariant,
    blockInnerReversal, localBlockEndpointVertexMap,
    blockLeftEndpointBase, delta, MonoidAlgebra.one_def]

/-- The endpoint's actual raw effect.  This is retained before the
relation-action quotient, where it would be deliberately erased. -/
theorem blockRelationIntegralCoordinate_operator_endpoint
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    blockRelationIntegralCoordinate stage row
        (blockWholeRelationEulerOperator seedOccurrence.root stage
          (localBlockEndpointBoundaryRelation stage)) =
      delta (1 : Units NNReal) -
        delta (blockPrimeScaleUnit (rowPrime row)) := by
  rw [blockRelationIntegralCoordinate_operator,
    blockRelationIntegralCoordinate_endpoint,
    leftTranslation_delta, mul_one]

end
end RawEffect
end ActionCofiber
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
