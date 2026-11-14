import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Model.Family.Words.Dynamic.Hilbert.SourceWord.ObservedCode.Future.Growth.Receiver.EvenBirth
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Receiver.PersistentRecoveryGain

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordEvenBirthOptimal

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

def fineRead (depth : Nat) : Nat → ZMod 2 :=
  SourceWordObservedCode.readAt (inventoryBound (runtimeAt (depth + 1)))
    (SourceWordEvenBirth.newWord depth)

def forget : ZMod 2 → ZMod 2 := fun _ => 0

theorem fine_diff (depth : Nat) (even : Even depth) :
    fineRead depth 0 ≠ fineRead depth 1 := by
  have source := SourceWordEvenBirth.new_query_separates depth even
  simpa only [SourceWordObservedCode.source_query_read, fineRead,
    SourceWordEvenBirth.actorZero, SourceWordEvenBirth.actorOne] using source

theorem gain_pos (depth : Nat) (even : Even depth) :
    0 < SourceWordFieldCode.gGap (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth) (fineRead depth) forget := by
  have sourceGap : 0 < SourceConditionalMergeLoss.gap
      (runtimeAt (depth + 1)) (fineRead depth) forget := by
    apply SourceConditionalMergeLoss.gap_positive_of_collision
      (runtimeAt (depth + 1)) (fineRead depth) forget
      (SourceWordEvenBirth.actorZero depth) (SourceWordEvenBirth.actorOne depth)
    · rfl
    · exact fine_diff depth even
  have nonzero : SourceWordFieldCode.gGap (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth) (fineRead depth) forget ≠ 0 := by
    intro zero
    exact (ne_of_gt sourceGap) ((SourceWordFieldCode.gGap_zero_iff_source_gap
      (runtimeAt (depth + 1)) (SourceWordEvenBirth.newWord depth)
      (fineRead depth) forget).mp zero)
  exact lt_of_le_of_ne
    (SourceWordFieldCode.gGap_nonnegative (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth) (fineRead depth) forget)
    (Ne.symm nonzero)

theorem information_loss_pos (depth : Nat) (even : Even depth) :
    0 < SourceConditionalInformationLoss.amount
      (runtimeAt (depth + 1)) (fineRead depth) forget := by
  apply (SourceConditionalInformationLoss.amount_positive_iff_gap
    (runtimeAt (depth + 1)) (fineRead depth) forget).mpr
  apply SourceConditionalMergeLoss.gap_positive_of_collision
    (runtimeAt (depth + 1)) (fineRead depth) forget
    (SourceWordEvenBirth.actorZero depth) (SourceWordEvenBirth.actorOne depth)
  · rfl
  · exact fine_diff depth even

def oldBest (depth : Nat) : ZMod 2 → SourceJointClockGraph.Carrier :=
  SourceWordFieldCode.gCoarseMean (runtimeAt (depth + 1))
    (SourceWordEvenBirth.newWord depth) (fineRead depth) forget

def freshBest (depth : Nat) : ZMod 2 → SourceJointClockGraph.Carrier :=
  SourceWordFieldCode.gFineMean (runtimeAt (depth + 1))
    (SourceWordEvenBirth.newWord depth) (fineRead depth)

theorem old_risk_eq (depth : Nat) (even : Even depth) :
    SourceWordCodeRisk.risk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth) (SourceWordEvenBirth.oldCode depth)
      (oldBest depth) =
    SourceWordFieldCode.gRisk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth) (forget ∘ fineRead depth)
      (oldBest depth) := by
  apply SourceWordPersistentRecoveryGain.bit_risk_eq_gRisk_of_query_eq
  intro actor
  rw [SourceWordEvenBirth.oldCode_query_zero depth even actor]
  rfl

theorem fresh_risk_eq (depth : Nat) :
    SourceWordCodeRisk.risk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth)
      (SourceWordObservedCode.encodeObserved (runtimeAt (depth + 1))
        (SourceWordEvenBirth.newWord depth)) (freshBest depth) =
    SourceWordFieldCode.gRisk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth) (fineRead depth)
      (freshBest depth) := by
  apply SourceWordPersistentRecoveryGain.bit_risk_eq_gRisk_of_query_eq
  intro actor
  rw [SourceWordObservedCode.query_actual]
  rfl

theorem exact_gain (depth : Nat) (even : Even depth) :
    SourceWordCodeRisk.risk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth) (SourceWordEvenBirth.oldCode depth)
      (oldBest depth) =
    SourceWordCodeRisk.risk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth)
      (SourceWordObservedCode.encodeObserved (runtimeAt (depth + 1))
        (SourceWordEvenBirth.newWord depth)) (freshBest depth) +
    SourceWordFieldCode.gGap (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth) (fineRead depth) forget := by
  rw [old_risk_eq depth even, fresh_risk_eq depth]
  exact SourceWordFieldCode.gRisk_refinement
    (runtimeAt (depth + 1)) (SourceWordEvenBirth.newWord depth)
    (fineRead depth) forget

theorem strict_gain (depth : Nat) (even : Even depth) :
    SourceWordCodeRisk.risk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth)
      (SourceWordObservedCode.encodeObserved (runtimeAt (depth + 1))
        (SourceWordEvenBirth.newWord depth)) (freshBest depth) <
    SourceWordCodeRisk.risk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth) (SourceWordEvenBirth.oldCode depth)
      (oldBest depth) := by
  rw [exact_gain depth even]
  exact lt_add_of_pos_right _ (gain_pos depth even)

end
end SourceWordEvenBirthOptimal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
