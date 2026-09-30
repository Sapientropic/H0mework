import H0mework.Fock.PrimeFieldJoint.JointConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointTime

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedAcquisitionMeasure
open SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev NextSpace (depth bound : Nat) :=
  SourceOwnedObservationHistory.Space nativeStep (rawWords depth)
    (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound

abbrev timeTransfer (depth bound : Nat) : FieldSpace depth bound →L[ℂ] NextSpace depth bound :=
  IsometricRetainedTransfer.transfer
    (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)

def nextWord (depth bound : Nat) : NextSpace depth bound →ₗ[ℂ] Nat →₀ ℂ :=
  ∑ index : Fin (bound + 1), (Finsupp.lsingle (runtimeAt index.val).tick.next.state).comp
    ((SourceHistoryWord.coefficient bound index).comp (Actor.nextPullback depth bound).toLinearMap)

theorem next_address (bound : Nat) (index : Fin (bound + 1)) :
    (runtimeAt index.val).tick.next.state = index.val + 1 := runtimeAt_state (index.val + 1)

theorem next_sample_actual (depth bound : Nat) (index : Fin (bound + 1)) :
    Actor.nextRead depth bound index = fieldPoint nativeStep (rawWords depth)
      ((runtimeAt index.val).tick.next.current.visit.current : Current) := by
  exact (next_read_actual depth bound index).trans
    (original_point depth ((runtimeAt (index.val + 1)).current.visit.current : Current))

theorem next_word_is_source_push (depth bound : Nat) (value : NextSpace depth bound) :
    nextWord depth bound value = push ℂ
      (SourceHistoryWord.word bound (Actor.nextPullback depth bound value)) := by
  rw [nextWord, LinearMap.sum_apply, SourceHistoryWord.word_sum, map_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, next_address, push,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

def nextJoint (depth bound : Nat) : NextSpace depth bound →ₗ[ℂ] SourceMassCompletion.Joint :=
  SourceMassCompletion.jointRead.comp (nextWord depth bound)

theorem next_word_transfer (depth bound : Nat) (value : FieldSpace depth bound) :
    nextWord depth bound (timeTransfer depth bound value) =
      push ℂ (SourceGeneratedAcquisitionJoint.word depth bound value) := by
  rw [next_word_is_source_push]
  have actual := DFunLike.congr_fun (SourceGeneratedRecordFrame.joint_action_square depth bound) value
  change Actor.nextPullback depth bound (timeTransfer depth bound value) = Actor.currentPullback depth bound value at actual
  rw [actual]
  rfl

theorem next_joint_transfer (depth bound : Nat) (value : FieldSpace depth bound) :
    nextJoint depth bound (timeTransfer depth bound value) =
      SourceMassCompletion.action (SourceGeneratedAcquisitionJoint.joint depth bound value) := by
  change SourceMassCompletion.jointRead (nextWord depth bound (timeTransfer depth bound value)) = _
  rw [next_word_transfer]
  exact (SourceMassCompletion.action_source (SourceGeneratedAcquisitionJoint.word depth bound value)).symm

end
end SourceGeneratedJointTime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
