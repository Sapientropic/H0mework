import H0mework.Versions.Y.Arithmetic.BlockSpecialization.CokernelRead

/-!
# Successor naturality of the arithmetic block-cokernel read

The existing integral relation restriction commutes with `id - Euler` and
therefore descends to the arithmetic action-cokernel.  The finite-stage block
cokernel read commutes with the source and target restrictions.  This is a
stagewise naturality result only; no limit/base-change interchange is used.
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
namespace BlockActionCokernelNaturality

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open CanonicalUnitArithmeticFactorizationWholeHistoryIntegralRelationEmbedding
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection
open BlockArithmeticSpecializationStage
open BlockArithmeticSpecializationWholeComplex
open BlockArithmeticSpecializationEndpoint
open BlockActionCokernelRead

noncomputable section

theorem integralRelationOperator_restriction_square (stage : Nat) :
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction
        seedOccurrence.root stage).comp
        (integralRelationEulerOperator (stage + 1)) =
      (integralRelationEulerOperator stage).comp
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction
          seedOccurrence.root stage) := by
  unfold integralRelationEulerOperator
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction_euler_square]

theorem integralOperatorRange_restriction (stage : Nat) :
    LinearMap.range (integralRelationEulerOperator (stage + 1)) ≤
      (LinearMap.range (integralRelationEulerOperator stage)).comap
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction
          seedOccurrence.root stage) := by
  rintro value ⟨preimage, rfl⟩
  refine ⟨CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction
      seedOccurrence.root stage preimage, ?_⟩
  exact (LinearMap.congr_fun
    (integralRelationOperator_restriction_square stage) preimage).symm

def integralRelationOperatorCokernelRestriction (stage : Nat) :
    IntegralRelationOperatorCokernel (stage + 1) →ₗ[ℤ]
      IntegralRelationOperatorCokernel stage :=
  Submodule.mapQ
    (LinearMap.range (integralRelationEulerOperator (stage + 1)))
    (LinearMap.range (integralRelationEulerOperator stage))
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction
      seedOccurrence.root stage)
    (integralOperatorRange_restriction stage)

theorem localEndpointBoundaryRelation_integral_restriction (stage : Nat) :
    CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction
        seedOccurrence.root stage
        (localEndpointBoundaryRelation (stage + 1)) =
      localEndpointBoundaryRelation stage := by
  funext row
  change carrierRestriction seedOccurrence.root stage
      (localInnerEmbedding seedOccurrence.root (stage + 1)
        endpointAntiInvariantBase) =
    localInnerEmbedding seedOccurrence.root stage endpointAntiInvariantBase
  exact carrierRestriction_localInnerEmbedding seedOccurrence.root stage
    endpointAntiInvariantBase

theorem integralRelationOperatorCokernelRestriction_endpointClass
    (stage : Nat) :
    integralRelationOperatorCokernelRestriction stage
        (specializedIntegralEndpointBoundaryClass (stage + 1)) =
      specializedIntegralEndpointBoundaryClass stage := by
  unfold integralRelationOperatorCokernelRestriction
    specializedIntegralEndpointBoundaryClass
    integralRelationOperatorCokernelProjection
  change Submodule.Quotient.mk
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction
        seedOccurrence.root stage
        (localEndpointBoundaryRelation (stage + 1))) =
    Submodule.Quotient.mk (localEndpointBoundaryRelation stage)
  exact congrArg Submodule.Quotient.mk
    (localEndpointBoundaryRelation_integral_restriction stage)

theorem blockWholeRelationSemilinearRead_restriction_square
    (stage : Nat) :
    (blockWholeRelationSemilinearRead stage).comp
        (blockWholeRelationRestriction seedOccurrence.root stage) =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction
        seedOccurrence.root stage).comp
        (blockWholeRelationSemilinearRead (stage + 1)) := by
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (blockWholeRelationRead_restriction_square seedOccurrence.root stage) value

/-- The arithmetic quotient read is natural for the actual source successor. -/
theorem blockRelationActionCokernelArithmeticRead_restriction_square
    (stage : Nat) :
    (blockRelationActionCokernelArithmeticRead stage).comp
        (localRelationActionCokernelRestriction stage) =
      (integralRelationOperatorCokernelRestriction stage).comp
        (blockRelationActionCokernelArithmeticRead (stage + 1)) := by
  apply LinearMap.ext
  intro quotient
  refine Submodule.Quotient.induction_on _ quotient ?_
  intro value
  change Submodule.Quotient.mk
      (blockWholeRelationSemilinearRead stage
        (blockWholeRelationRestriction seedOccurrence.root stage value)) =
    Submodule.Quotient.mk
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction
        seedOccurrence.root stage
        (blockWholeRelationSemilinearRead (stage + 1) value))
  exact congrArg Submodule.Quotient.mk
    (LinearMap.congr_fun
      (blockWholeRelationSemilinearRead_restriction_square stage) value)

end
end BlockActionCokernelNaturality
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
