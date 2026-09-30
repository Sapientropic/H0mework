import H0mework.Realization.Integral.CharacterDoubleDual
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Arithmetic.LivingLawCanonicalRiemannReceiptArithmeticComplexificationResidual

/-!
# Character perfectification of the receipt-owned integral arithmetic class

The nonzero global integral action-cokernel class enters the generic
character-double-dual exact image before any finite complexification.  Its
canonical character point is nonzero and the source theorem generates a
detecting rational-circle character.  The previously proved all-finite
complexification loss remains attached to the same receipt occurrence.

No character, separator, descent, or nondegeneracy witness is supplied by a
caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
namespace MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Arithmetic.Character

open SourceGeneratedCharacterDoubleDualExactPerfectification
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalTower
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalOccurrence
open Arithmetic

noncomputable section

abbrev ReceiptArithmeticCharacterPerfectification :=
  ExactPerfectification (RestrictedArithmeticGlobalCokernel : Type)

def globalArithmeticEndpointCharacterPoint :
    ReceiptArithmeticCharacterPerfectification :=
  canonicalMap (RestrictedArithmeticGlobalCokernel : Type)
    globalSpecializedIntegralEndpointBoundaryClass

theorem globalArithmeticEndpointCharacterPoint_ne_zero :
    globalArithmeticEndpointCharacterPoint ≠ 0 := by
  intro vanished
  apply globalSpecializedIntegralEndpointBoundaryClass_ne_zero
  apply canonicalMap_injective (RestrictedArithmeticGlobalCokernel : Type)
  simpa [globalArithmeticEndpointCharacterPoint] using vanished

theorem globalArithmeticEndpointCharacterPoint_evaluation :
    (globalArithmeticEndpointCharacterPoint :
      DoubleDual (RestrictedArithmeticGlobalCokernel : Type)) =
        evaluation (RestrictedArithmeticGlobalCokernel : Type)
          globalSpecializedIntegralEndpointBoundaryClass :=
  rfl

theorem exists_globalArithmeticEndpoint_detectingCharacter :
    ∃ character :
        CharacterModule (RestrictedArithmeticGlobalCokernel : Type),
      character globalSpecializedIntegralEndpointBoundaryClass ≠ 0 :=
  CharacterModule.exists_character_apply_ne_zero_of_ne_zero
    globalSpecializedIntegralEndpointBoundaryClass_ne_zero

def zeroOwnedReceiptArithmeticCharacterOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  (zeroOwnedReceiptArithmeticResidualOccurrence observation nontrivial).map
    fun source => (source, globalArithmeticEndpointCharacterPoint)

theorem zeroOwnedReceiptArithmeticCharacterOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedReceiptArithmeticCharacterOccurrence observation nontrivial).map
        Prod.fst =
      zeroOwnedReceiptArithmeticResidualOccurrence observation nontrivial := by
  unfold zeroOwnedReceiptArithmeticCharacterOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (zeroOwnedReceiptArithmeticResidualOccurrence
    observation nontrivial).map id = _
  exact RootedAccountedUnfolding.map_id _

structure ZeroOwnedReceiptArithmeticCharacterPerfectificationCertificate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Type where
  occurrence_projects : type_of%
    (zeroOwnedReceiptArithmeticCharacterOccurrence_projects
      observation nontrivial)
  character_point_ne_zero : globalArithmeticEndpointCharacterPoint ≠ 0
  character_point_evaluation : type_of%
    globalArithmeticEndpointCharacterPoint_evaluation
  source_generates_detecting_character : type_of%
    exists_globalArithmeticEndpoint_detectingCharacter
  retains_finite_complexification_residual : ∀ stage,
    type_of% (globalArithmeticEndpoint_complexLocalRead_zero stage)

def generateZeroOwnedReceiptArithmeticCharacterPerfectificationCertificate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ZeroOwnedReceiptArithmeticCharacterPerfectificationCertificate
      observation nontrivial where
  occurrence_projects :=
    zeroOwnedReceiptArithmeticCharacterOccurrence_projects
      observation nontrivial
  character_point_ne_zero := globalArithmeticEndpointCharacterPoint_ne_zero
  character_point_evaluation := globalArithmeticEndpointCharacterPoint_evaluation
  source_generates_detecting_character :=
    exists_globalArithmeticEndpoint_detectingCharacter
  retains_finite_complexification_residual :=
    globalArithmeticEndpoint_complexLocalRead_zero

end
end MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Arithmetic.Character
end NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
