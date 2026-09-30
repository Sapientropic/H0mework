import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Perfectification.Character.LivingLawCanonicalRiemannReceiptArithmeticCharacterPerfectification

/-!
# Source-generated stage-three arithmetic character

The actual prime-three row makes the integral boundary coordinate descend
through the finite `1 - Euler` cokernel to the rational circle.  Its local
endpoint value is nonzero.  Precomposition with the existing global
restriction therefore gives a concrete global character detecting the
nonzero integral endpoint class and the canonical character-perfectification
point.

This removes the arbitrary detecting-character choice.  It does not yet
identify the arithmetic phase with the zero-owned Mellin phase.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
namespace MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Arithmetic.Character

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection
open SourceGeneratedCharacterDoubleDualExactPerfectification
open NoIslandNoMagic.CanonicalArithmeticState.BlockArithmeticSpecializationEndpoint
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalTower
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalOccurrence
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

def stageThreeBoundaryPhase :
    WholeRelationModule seedOccurrence.root 3 →ₗ[ℤ] AddCircle (1 : ℚ) :=
  (CharacterModule.int.divByNat 2).toIntLinearMap.comp
    (integralBoundaryCoordinate 3 actualStageThreePrimeRow)

theorem stageThreeBoundaryPhase_operator_zero
    (value : WholeRelationModule seedOccurrence.root 3) :
    stageThreeBoundaryPhase (integralRelationEulerOperator 3 value) = 0 := by
  rw [stageThreeBoundaryPhase, LinearMap.comp_apply,
    integralBoundaryCoordinate_operator,
    actualStageThreePrimeRow_prime]
  change CharacterModule.int.divByNat 2
      ((1 - 3) * integralBoundaryCoordinate 3 actualStageThreePrimeRow value) = 0
  calc
    _ = CharacterModule.int.divByNat 2
        ((-integralBoundaryCoordinate 3 actualStageThreePrimeRow value) •
          (2 : ℤ)) := by
            congr 1
            simp [mul_comm]
    _ = (-integralBoundaryCoordinate 3 actualStageThreePrimeRow value) •
        CharacterModule.int.divByNat 2 (2 : ℤ) := by
          rw [map_zsmul]
    _ = 0 := by
      have twoZero : CharacterModule.int.divByNat 2 (2 : ℤ) = 0 :=
        CharacterModule.int.divByNat_self 2
      rw [twoZero, smul_zero]

theorem integralRelationOperatorRange_le_stageThreeBoundaryPhase_ker :
    LinearMap.range (integralRelationEulerOperator 3) ≤
      LinearMap.ker stageThreeBoundaryPhase := by
  rintro _ ⟨value, rfl⟩
  rw [LinearMap.mem_ker]
  exact stageThreeBoundaryPhase_operator_zero value

def stageThreeEndpointCharacter :
    CharacterModule (IntegralRelationOperatorCokernel 3) :=
  (Submodule.liftQ
    (LinearMap.range (integralRelationEulerOperator 3))
    stageThreeBoundaryPhase
    integralRelationOperatorRange_le_stageThreeBoundaryPhase_ker).toAddMonoidHom

theorem divByTwo_one_ne_zero :
    CharacterModule.int.divByNat 2 (1 : ℤ) ≠ 0 := by
  have evaluation : CharacterModule.int.divByNat 2 (1 : ℤ) =
      ((2⁻¹ : ℚ) : AddCircle (1 : ℚ)) := by
    change (1 : ℤ) • ((2⁻¹ : ℚ) : AddCircle (1 : ℚ)) = _
    simp
  rw [evaluation]
  change ((2⁻¹ : ℚ) : AddCircle (1 : ℚ)) ≠ 0
  intro vanished
  rw [AddCircle.coe_eq_zero_iff] at vanished
  rcases vanished with ⟨integer, equality⟩
  have denominator := congrArg Rat.den equality
  norm_num at denominator

theorem stageThreeEndpointCharacter_endpoint_ne_zero :
    stageThreeEndpointCharacter
        (specializedIntegralEndpointBoundaryClass 3) ≠ 0 := by
  change stageThreeBoundaryPhase (localEndpointBoundaryRelation 3) ≠ 0
  rw [stageThreeBoundaryPhase, LinearMap.comp_apply,
    integralBoundaryCoordinate_endpoint]
  exact divByTwo_one_ne_zero

def globalStageThreeEndpointCharacter :
    CharacterModule (RestrictedArithmeticGlobalCokernel : Type) :=
  stageThreeEndpointCharacter.comp
    (limit.π restrictedArithmeticCokernelDiagram
      (Opposite.op 3)).hom.toAddMonoidHom

theorem globalStageThreeEndpointCharacter_endpoint_ne_zero :
    globalStageThreeEndpointCharacter
        globalSpecializedIntegralEndpointBoundaryClass ≠ 0 := by
  change stageThreeEndpointCharacter
      ((limit.π restrictedArithmeticCokernelDiagram
        (Opposite.op 3)).hom
          globalSpecializedIntegralEndpointBoundaryClass) ≠ 0
  rw [globalSpecializedIntegralEndpointBoundaryClass_restriction]
  exact stageThreeEndpointCharacter_endpoint_ne_zero

theorem globalArithmeticEndpointCharacterPoint_stageThree_read :
    (globalArithmeticEndpointCharacterPoint :
      DoubleDual (RestrictedArithmeticGlobalCokernel : Type))
        globalStageThreeEndpointCharacter =
      globalStageThreeEndpointCharacter
        globalSpecializedIntegralEndpointBoundaryClass := by
  rw [globalArithmeticEndpointCharacterPoint_evaluation,
    evaluation_apply]

theorem globalArithmeticEndpointCharacterPoint_stageThree_read_ne_zero :
    (globalArithmeticEndpointCharacterPoint :
      DoubleDual (RestrictedArithmeticGlobalCokernel : Type))
        globalStageThreeEndpointCharacter ≠ 0 := by
  rw [globalArithmeticEndpointCharacterPoint_stageThree_read]
  exact globalStageThreeEndpointCharacter_endpoint_ne_zero

def zeroOwnedReceiptStageThreeCharacterOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  (zeroOwnedReceiptArithmeticCharacterOccurrence observation nontrivial).map
    fun source => (source, globalStageThreeEndpointCharacter)

theorem zeroOwnedReceiptStageThreeCharacterOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedReceiptStageThreeCharacterOccurrence observation nontrivial).map
        Prod.fst =
      zeroOwnedReceiptArithmeticCharacterOccurrence observation nontrivial := by
  unfold zeroOwnedReceiptStageThreeCharacterOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (zeroOwnedReceiptArithmeticCharacterOccurrence
    observation nontrivial).map id = _
  exact RootedAccountedUnfolding.map_id _

structure ZeroOwnedReceiptStageThreeArithmeticCharacterCertificate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Type where
  occurrence_projects : type_of%
    (zeroOwnedReceiptStageThreeCharacterOccurrence_projects
      observation nontrivial)
  operator_range_zero : ∀ value,
    type_of% (stageThreeBoundaryPhase_operator_zero value)
  local_endpoint_read_ne_zero :
    type_of% stageThreeEndpointCharacter_endpoint_ne_zero
  global_endpoint_read_ne_zero :
    type_of% globalStageThreeEndpointCharacter_endpoint_ne_zero
  canonical_point_read_ne_zero :
    type_of% globalArithmeticEndpointCharacterPoint_stageThree_read_ne_zero

def generateZeroOwnedReceiptStageThreeArithmeticCharacterCertificate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ZeroOwnedReceiptStageThreeArithmeticCharacterCertificate
      observation nontrivial where
  occurrence_projects := zeroOwnedReceiptStageThreeCharacterOccurrence_projects
    observation nontrivial
  operator_range_zero := stageThreeBoundaryPhase_operator_zero
  local_endpoint_read_ne_zero := stageThreeEndpointCharacter_endpoint_ne_zero
  global_endpoint_read_ne_zero :=
    globalStageThreeEndpointCharacter_endpoint_ne_zero
  canonical_point_read_ne_zero :=
    globalArithmeticEndpointCharacterPoint_stageThree_read_ne_zero

end
end MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Arithmetic.Character
end NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
