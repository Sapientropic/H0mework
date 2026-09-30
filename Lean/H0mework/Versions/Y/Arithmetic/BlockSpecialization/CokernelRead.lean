import H0mework.Versions.Y.Arithmetic.BlockSpecialization.Endpoint
import H0mework.Versions.Y.Arithmetic.EulerDerived.EndpointCokernelState

/-!
# Arithmetic read of the universal block action cokernel

The arithmetic coefficient specialization is retained as a semilinear map.
It carries the universal block relation operator `id - M` to the existing
integral relation operator and therefore descends to their action cokernels.

The literal block endpoint class maps to the quotient class of the already
installed integral endpoint boundary.  No inverse-limit base-change or
vanishing assertion enters this finite-stage construction.
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
namespace BlockActionCokernelRead

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDeterminantSupport
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection
open BlockArithmeticSpecializationStage
open BlockArithmeticSpecializationWholeComplex
open BlockArithmeticSpecializationEndpoint

noncomputable section

abbrev IntegralRelationOperatorCokernel (stage : Nat) :=
  (WholeRelationModule seedOccurrence.root stage) ⧸
    LinearMap.range (integralRelationEulerOperator stage)

def integralRelationOperatorCokernelProjection (stage : Nat) :
    WholeRelationModule seedOccurrence.root stage →ₗ[ℤ]
      IntegralRelationOperatorCokernel stage :=
  Submodule.mkQ _

/-- The existing arithmetic endpoint boundary, viewed in the integral
`id - Euler` cokernel. -/
def specializedIntegralEndpointBoundaryClass (stage : Nat) :
    IntegralRelationOperatorCokernel stage :=
  integralRelationOperatorCokernelProjection stage
    (localEndpointBoundaryRelation stage)

/-- The coefficient read as an actual semilinear map. -/
def blockWholeRelationSemilinearRead (stage : Nat) :
    BlockWholeRelation seedOccurrence.root stage →ₛₗ[
      actualBlockSpecialization]
      WholeRelationModule seedOccurrence.root stage where
  toFun := blockWholeRelationRead seedOccurrence.root stage
  map_add' := (blockWholeRelationRead seedOccurrence.root stage).map_add
  map_smul' := by
    intro coefficient value
    funext row
    exact blockInnerCarrierRead_block_smul seedOccurrence.root stage
      coefficient (value row)

/-- The arithmetic read carries the complete universal relation operator to
the already installed integral operator. -/
theorem blockWholeRelationRead_operator_square (stage : Nat) :
    (blockWholeRelationSemilinearRead stage).comp
        (blockWholeRelationEulerOperator seedOccurrence.root stage) =
      (integralRelationEulerOperator stage).comp
        (blockWholeRelationSemilinearRead stage) := by
  apply LinearMap.ext
  intro value
  change blockWholeRelationRead seedOccurrence.root stage
      (value - blockWholeRelationAction seedOccurrence.root stage value) =
    blockWholeRelationRead seedOccurrence.root stage value -
      relationEulerAction seedOccurrence.root stage
        (blockWholeRelationRead seedOccurrence.root stage value)
  rw [map_sub]
  exact congrArg
    (fun actionRead => blockWholeRelationRead seedOccurrence.root stage value -
      actionRead)
    (LinearMap.congr_fun
      (blockWholeRelationRead_action_square seedOccurrence.root stage) value)

theorem blockOperatorRange_maps_to_integralOperatorRange (stage : Nat) :
    LinearMap.range
        (blockWholeRelationEulerOperator seedOccurrence.root stage) ≤
      (LinearMap.range (integralRelationEulerOperator stage)).comap
        (blockWholeRelationSemilinearRead stage) := by
  rintro value ⟨preimage, rfl⟩
  refine ⟨blockWholeRelationSemilinearRead stage preimage, ?_⟩
  exact (LinearMap.congr_fun
    (blockWholeRelationRead_operator_square stage) preimage).symm

/-- The induced finite-stage semilinear map from the symbolic block
action-cokernel to the existing arithmetic action-cokernel. -/
def blockRelationActionCokernelArithmeticRead (stage : Nat) :
    LocalRelationActionCokernel stage →ₛₗ[actualBlockSpecialization]
      IntegralRelationOperatorCokernel stage :=
  Submodule.mapQ
    (LinearMap.range
      (blockWholeRelationEulerOperator seedOccurrence.root stage))
    (LinearMap.range (integralRelationEulerOperator stage))
    (blockWholeRelationSemilinearRead stage)
    (blockOperatorRange_maps_to_integralOperatorRange stage)

@[simp] theorem blockRelationActionCokernelArithmeticRead_mk
    (stage : Nat) (value : BlockWholeRelation seedOccurrence.root stage) :
    blockRelationActionCokernelArithmeticRead stage
        (localRelationActionCokernelProjection stage value) =
      integralRelationOperatorCokernelProjection stage
        (blockWholeRelationRead seedOccurrence.root stage value) := by
  rfl

/-- The universal endpoint class maps literally to the existing arithmetic
endpoint boundary class. -/
@[simp] theorem blockRelationActionCokernelArithmeticRead_endpointClass
    (stage : Nat) :
    blockRelationActionCokernelArithmeticRead stage
        (localEndpointBoundaryCokernelClass stage) =
      specializedIntegralEndpointBoundaryClass stage := by
  unfold localEndpointBoundaryCokernelClass
    specializedIntegralEndpointBoundaryClass
  rw [blockRelationActionCokernelArithmeticRead_mk,
    localBlockEndpointBoundaryRelation_arithmetic_read]

/-- At an actual prime-three row the arithmetic endpoint class survives. -/
theorem specializedIntegralEndpointBoundaryClass_ne_zero_at_three
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (primeThree : (rowPrime row : Nat) = 3) :
    specializedIntegralEndpointBoundaryClass stage ≠ 0 := by
  intro vanished
  have membership : localEndpointBoundaryRelation stage ∈
      LinearMap.range (integralRelationEulerOperator stage) :=
    (Submodule.Quotient.mk_eq_zero _).mp vanished
  rcases membership with ⟨preimage, equality⟩
  exact localEndpointBoundary_not_operator_range_at_three
    stage row primeThree ⟨preimage, equality.symm⟩

theorem mappedBlockEndpointClass_ne_zero_at_three
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (primeThree : (rowPrime row : Nat) = 3) :
    blockRelationActionCokernelArithmeticRead stage
        (localEndpointBoundaryCokernelClass stage) ≠ 0 := by
  rw [blockRelationActionCokernelArithmeticRead_endpointClass]
  exact specializedIntegralEndpointBoundaryClass_ne_zero_at_three
    stage row primeThree

abbrev ActualBlockCokernelArithmeticReadPayload (stage : Nat) :=
  FactorizationPayload ×
    (LocalRelationActionCokernel stage →ₛₗ[actualBlockSpecialization]
      IntegralRelationOperatorCokernel stage)

def actualBlockCokernelArithmeticReadOccurrence (stage : Nat) :
    RootedAccountedUnfolding
      (ActualBlockCokernelArithmeticReadPayload stage) :=
  (stageOccurrenceFrom seedOccurrence.root stage).map fun owner =>
    (owner, blockRelationActionCokernelArithmeticRead stage)

theorem actualBlockCokernelArithmeticReadOccurrence_projects (stage : Nat) :
    (actualBlockCokernelArithmeticReadOccurrence stage).map Prod.fst =
      stageOccurrenceFrom seedOccurrence.root stage := by
  unfold actualBlockCokernelArithmeticReadOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (stageOccurrenceFrom seedOccurrence.root stage).map id = _
  exact RootedAccountedUnfolding.map_id _

end
end BlockActionCokernelRead
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
