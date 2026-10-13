import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeSourceReturn.Inventory
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeSourceReturn.Payment
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
open Complex MeasureTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
local instance consumerGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem actual_native_source_return (ordinal : Nat) :
    actualReturnWriteRead observation nontrivial half depth ordinal =
      pairedPacking (Prior.originalK observation nontrivial half +
        OriginalKCombPhysicalAction.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal)) := by
  rw [actual_return_write_read, actualReturnValue, actualReturnEffect, ← map_add]

theorem actual_original_K_price (ordinal : Nat) :
    inner ℂ (Prior.originalK observation nontrivial half) (actualReturnWriteRead observation nontrivial half depth ordinal).1.1 =
      inner ℂ (Prior.originalK observation nontrivial half) (Prior.originalK observation nontrivial half) +
        inner ℂ (Prior.originalK observation nontrivial half)
          (OriginalKCombPhysicalAction.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal)) := by
  rw [actual_native_source_return]
  change inner ℂ (Prior.originalK observation nontrivial half) (_ + _) = _
  exact inner_add_right _ _ _

theorem actual_original_FourierK_price (ordinal : Nat) :
    inner ℂ (Prior.originalFourierK observation nontrivial half) (actualReturnWriteRead observation nontrivial half depth ordinal).1.2 =
      inner ℂ (Prior.originalFourierK observation nontrivial half) (Prior.originalFourierK observation nontrivial half) +
        inner ℂ (Prior.originalFourierK observation nontrivial half)
          (fourierL2 (OriginalKCombPhysicalAction.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal))) := by
  rw [actual_native_source_return]
  change inner ℂ (Prior.originalFourierK observation nontrivial half) (fourierL2 (_ + _)) = _
  rw [map_add, inner_add_right]
  rfl

theorem actual_initial_original_K (ordinal : Nat) :
    CF.collapseValue (returnPacket observation nontrivial half depth ordinal).1
      (receipt observation nontrivial half depth ordinal).2.2.1 =
      pairedPacking (Prior.originalK observation nontrivial half) :=
  actual_complete_source_value observation nontrivial half depth ordinal

-- Restoring the original field does not erase an actual source increment.
theorem actual_return_keeps_delta (ordinal : Nat) :
    (actualReturnWriteRead observation nontrivial half depth ordinal).1.1 = Prior.originalK observation nontrivial half ↔
      actualDelta observation nontrivial half depth ordinal = 0 := by
  rw [actual_native_source_return]
  change Prior.originalK observation nontrivial half +
    OriginalKCombPhysicalAction.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal) =
      Prior.originalK observation nontrivial half ↔ _
  constructor
  · intro erased
    have effectZero : OriginalKCombPhysicalAction.R observation nontrivial half
        (actualDelta observation nontrivial half depth ordinal) = 0 :=
      add_left_cancel (erased.trans (add_zero _).symm)
    rw [OriginalKCombCofinalRAction.original_R_direct] at effectZero
    exact burnolDirectRightResolvent_reflects_zero (observation.coordinate / 2)
      (OriginalKCombCofinalRAction.parameter_rightQuarter observation half) _ effectZero
  · intro zero
    rw [zero, map_zero, add_zero]

def actualCochainWord (ordinal : Nat) :=
  SaturationMonoid.SourceOperationCochain.updateWord (material observation nontrivial half depth ordinal).raw
theorem actual_cochain_update (ordinal : Nat) :
    SourceOperationRelations.evaluation
      (mixedEnvironment (material observation nontrivial half depth ordinal).environment
        (material observation nontrivial half depth ordinal).increment)
      (actualCochainWord observation nontrivial half depth ordinal) = 0 :=
  SaturationMonoid.SourceOperationCochain.evaluation_updateWord _ _ _

theorem consume_actual_source_return (ordinal : Nat) :
    actualReturnWriteRead observation nontrivial half depth ordinal =
      pairedPacking (Prior.originalK observation nontrivial half +
        OriginalKCombPhysicalAction.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_return_whole observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_return_next observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_action_payment observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_input_stage_payment observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_source_word_inventory observation nontrivial half depth ordinal)) ∧
    (type_of% (actual_input_stage_word_inventory observation nontrivial half depth ordinal)) :=
  ⟨actual_native_source_return observation nontrivial half depth ordinal,
    actual_return_whole observation nontrivial half depth ordinal,
    actual_return_next observation nontrivial half depth ordinal,
    actual_action_payment observation nontrivial half depth ordinal,
    actual_input_stage_payment observation nontrivial half depth ordinal,
    actual_source_word_inventory observation nontrivial half depth ordinal,
    actual_input_stage_word_inventory observation nontrivial half depth ordinal⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
