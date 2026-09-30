import H0mework.Probability.HistoryWord.Density
import H0mework.Probability.HistoryWord.Moments
import H0mework.Fock.PrimeHistoryMeasure.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionJoint

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedAcquisitionMeasure
open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceSuccessorBoundary
open SourceOwnedObservationHistory.SourceShift
noncomputable section

def word (depth bound : Nat) : FieldSpace depth bound →ₗ[ℂ] Nat →₀ ℂ :=
  (SourceHistoryWord.word bound).comp (Actor.currentPullback depth bound).toLinearMap

def hilbert (depth bound : Nat) : FieldSpace depth bound →ₗᵢ[ℂ] H :=
  (SourceHistoryWord.hilbert bound).comp (Actor.currentPullback depth bound)

def joint (depth bound : Nat) : FieldSpace depth bound →ₗ[ℂ] SourceMassCompletion.Joint :=
  SourceMassCompletion.jointRead.comp (word depth bound)

def density (depth bound : Nat) : FieldSpace depth bound :=
  Actor.currentTransfer depth bound (SourceHistoryWord.density bound)

theorem word_from_actor (depth bound : Nat) (value : SourceWeightedRecovery.Space (historyPMF bound)) :
    word depth bound (Actor.currentTransfer depth bound value) = SourceHistoryWord.word bound value := by
  change SourceHistoryWord.word bound
    (Actor.currentPullback depth bound (Actor.currentTransfer depth bound value)) = _
  rw [actor_transfer_samples]

theorem density_word (depth bound : Nat) : word depth bound (density depth bound) = meanWord bound := by
  rw [density, word_from_actor, SourceHistoryWord.density_word]

theorem density_joint (depth bound : Nat) :
    joint depth bound (density depth bound) = SourceMassCompletion.jointRead (meanWord bound) :=
  congrArg SourceMassCompletion.jointRead (density_word depth bound)

theorem first_joint (depth bound : Nat) (value : FieldSpace depth bound) :
    SourceMassCompletion.firstRead (joint depth bound value) = hilbert depth bound value := rfl

theorem mass_joint (depth bound : Nat) (value : FieldSpace depth bound) :
    SourceMassCompletion.massRead (joint depth bound value) =
      Real.sqrt (bound + 1 : ℝ) • ∫ index, Actor.currentPullback depth bound value index ∂(historyPMF bound).toMeasure :=
  SourceHistoryWord.mass_original_mean bound _

theorem joint_norm_sq (depth bound : Nat) (value : FieldSpace depth bound) :
    ‖joint depth bound value‖ ^ 2 = ‖value‖ ^ 2 + (bound + 1 : ℝ) *
      ‖∫ index, Actor.currentPullback depth bound value index ∂(historyPMF bound).toMeasure‖ ^ 2 := by
  have original := SourceHistoryWord.joint_norm_sq bound (Actor.currentPullback depth bound value)
  rw [(Actor.currentPullback depth bound).norm_map] at original
  exact original

def normalize (oldDepth freshDepth : Nat) {old fresh : Nat} (retained : old ≤ fresh) :
    FieldSpace oldDepth old →L[ℂ] FieldSpace freshDepth fresh :=
  (Actor.currentTransfer freshDepth fresh).comp
    ((SourceHistoryGrowth.normalizedInclusion retained).toContinuousLinearMap.comp
      (Actor.currentPullback oldDepth old).toContinuousLinearMap)

theorem normalize_word (oldDepth freshDepth : Nat) {old fresh : Nat} (retained : old ≤ fresh)
    (value : FieldSpace oldDepth old) :
    word freshDepth fresh (normalize oldDepth freshDepth retained value) = word oldDepth old value := by
  change word freshDepth fresh (Actor.currentTransfer freshDepth fresh
    (SourceHistoryGrowth.normalizedInclusion retained (Actor.currentPullback oldDepth old value))) = _
  rw [word_from_actor, SourceHistoryWord.normalized_word]
  rfl

theorem normalize_joint (oldDepth freshDepth : Nat) {old fresh : Nat} (retained : old ≤ fresh)
    (value : FieldSpace oldDepth old) :
    joint freshDepth fresh (normalize oldDepth freshDepth retained value) = joint oldDepth old value :=
  congrArg SourceMassCompletion.jointRead (normalize_word oldDepth freshDepth retained value)

theorem normalize_norm (oldDepth freshDepth : Nat) {old fresh : Nat} (retained : old ≤ fresh)
    (value : FieldSpace oldDepth old) : ‖normalize oldDepth freshDepth retained value‖ = ‖value‖ := by
  change ‖Actor.currentTransfer freshDepth fresh
    (SourceHistoryGrowth.normalizedInclusion retained (Actor.currentPullback oldDepth old value))‖ = _
  rw [actor_transfer_norm, (SourceHistoryGrowth.normalizedInclusion retained).norm_map,
    (Actor.currentPullback oldDepth old).norm_map]

end
end SourceGeneratedAcquisitionJoint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
