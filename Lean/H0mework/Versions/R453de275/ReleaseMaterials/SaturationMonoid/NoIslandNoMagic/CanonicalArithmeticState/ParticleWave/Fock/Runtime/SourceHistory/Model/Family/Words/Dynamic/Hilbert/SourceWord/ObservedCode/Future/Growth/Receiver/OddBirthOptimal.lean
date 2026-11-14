import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Model.Family.Words.Dynamic.Hilbert.SourceWord.ObservedCode.Future.Growth.Receiver.EvenBirthOptimal

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordOddBirth

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

theorem odd_old_bit_one (depth : Nat) (odd : Odd depth) :
    ((depth + 2 : Nat) : ZMod 2) = 1 := by
  rcases odd with ⟨half, rfl⟩
  have two : (2 : ZMod 2) = 0 := by decide
  calc
    _ = (2 : ZMod 2) * (half : ZMod 2) + 3 := by push_cast; ring
    _ = 1 := by rw [two]; simp only [zero_mul, zero_add]; decide

theorem odd_new_bit_zero (depth : Nat) (odd : Odd depth) :
    ((depth + 3 : Nat) : ZMod 2) = 0 := by
  rcases odd with ⟨half, rfl⟩
  have two : (2 : ZMod 2) = 0 := by decide
  calc
    _ = (2 : ZMod 2) * (half : ZMod 2) + 4 := by push_cast; ring
    _ = 0 := by rw [two]; simp only [zero_mul, zero_add]; decide

theorem old_query_native (depth : Nat) (odd : Odd depth)
    (actor : Actors (runtimeAt (depth + 1))) :
    SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth) actor =
        SourceWordObservedCode.readAt depth [] actor.val := by
  have action := SourceWordFutureBitGrowth.carried_fresh_query depth actor
  rw [SourceWordFreshReceiver.fresh_material_bit,
    odd_old_bit_one depth odd, mul_one] at action
  exact action

theorem new_query_zero (depth : Nat) (odd : Odd depth)
    (actor : Actors (runtimeAt (depth + 1))) :
    SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth) actor = 0 := by
  rw [SourceWordEvenBirth.newWord, SourceWordFreshReceiver.fresh_query_all,
    SourceWordFreshReceiver.fresh_material_bit, odd_new_bit_zero depth odd,
    mul_zero]

theorem old_query_separates (depth : Nat) (odd : Odd depth) :
    SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
        (SourceWordEvenBirth.oldWord depth) (SourceWordEvenBirth.actorZero depth) ≠
      SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
        (SourceWordEvenBirth.oldWord depth) (SourceWordEvenBirth.actorOne depth) := by
  rw [old_query_native depth odd, old_query_native depth odd]
  change SourceWordObservedCode.observe
      (nativeStep ((runtimeAt 0).current.visit.current : Current)) ≠
    SourceWordObservedCode.observe
      (nativeStep ((runtimeAt 1).current.visit.current : Current))
  decide

theorem new_future_same (depth : Nat) (odd : Odd depth)
    (left right : Actors (runtimeAt (depth + 1))) :
    SourceWordFutureBit.futureRead (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth) left =
    SourceWordFutureBit.futureRead (runtimeAt (depth + 1))
      (SourceWordEvenBirth.newWord depth) right :=
  (SourceWordFutureBit.future_kernel _ _ _ _).mpr
    ((new_query_zero depth odd left).trans (new_query_zero depth odd right).symm)

theorem old_future_separates (depth : Nat) (odd : Odd depth) :
    SourceWordFutureBit.futureRead (runtimeAt (depth + 1))
        (SourceWordEvenBirth.oldWord depth) (SourceWordEvenBirth.actorZero depth) ≠
      SourceWordFutureBit.futureRead (runtimeAt (depth + 1))
        (SourceWordEvenBirth.oldWord depth) (SourceWordEvenBirth.actorOne depth) := by
  intro same
  exact old_query_separates depth odd
    ((SourceWordFutureBit.future_kernel _ _ _ _).mp same)

theorem fresh_future_cannot_recover_old (depth : Nat) (odd : Odd depth)
    (decode : SourceWordEvenBirth.FutureResponse depth →
      SourceWordEvenBirth.FutureResponse depth) :
    ¬ ∀ actor : Actors (runtimeAt (depth + 1)),
      decode (SourceWordFutureBit.futureRead (runtimeAt (depth + 1))
        (SourceWordEvenBirth.newWord depth) actor) =
      SourceWordFutureBit.futureRead (runtimeAt (depth + 1))
        (SourceWordEvenBirth.oldWord depth) actor := by
  intro recovers
  exact old_future_separates depth odd
    ((recovers (SourceWordEvenBirth.actorZero depth)).symm.trans
      ((congrArg decode (new_future_same depth odd
        (SourceWordEvenBirth.actorZero depth) (SourceWordEvenBirth.actorOne depth))).trans
        (recovers (SourceWordEvenBirth.actorOne depth))))

def fineRead (depth : Nat) : Nat → ZMod 2 :=
  SourceWordObservedCode.readAt (inventoryBound (runtimeAt (depth + 1)))
    (SourceWordEvenBirth.oldWord depth)

def forget : ZMod 2 → ZMod 2 := fun _ => 0

theorem fine_diff (depth : Nat) (odd : Odd depth) :
    fineRead depth 0 ≠ fineRead depth 1 := by
  have source := old_query_separates depth odd
  simpa only [SourceWordObservedCode.source_query_read, fineRead,
    SourceWordEvenBirth.actorZero, SourceWordEvenBirth.actorOne] using source

theorem gain_pos (depth : Nat) (odd : Odd depth) :
    0 < SourceWordFieldCode.gGap (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth) (fineRead depth) forget := by
  have sourceGap : 0 < SourceConditionalMergeLoss.gap
      (runtimeAt (depth + 1)) (fineRead depth) forget := by
    apply SourceConditionalMergeLoss.gap_positive_of_collision
      (runtimeAt (depth + 1)) (fineRead depth) forget
      (SourceWordEvenBirth.actorZero depth) (SourceWordEvenBirth.actorOne depth)
    · rfl
    · exact fine_diff depth odd
  have nonzero : SourceWordFieldCode.gGap (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth) (fineRead depth) forget ≠ 0 := by
    intro zero
    exact (ne_of_gt sourceGap) ((SourceWordFieldCode.gGap_zero_iff_source_gap
      (runtimeAt (depth + 1)) (SourceWordEvenBirth.oldWord depth)
      (fineRead depth) forget).mp zero)
  exact lt_of_le_of_ne
    (SourceWordFieldCode.gGap_nonnegative (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth) (fineRead depth) forget)
    (Ne.symm nonzero)

theorem information_loss_pos (depth : Nat) (odd : Odd depth) :
    0 < SourceConditionalInformationLoss.amount
      (runtimeAt (depth + 1)) (fineRead depth) forget := by
  apply (SourceConditionalInformationLoss.amount_positive_iff_gap
    (runtimeAt (depth + 1)) (fineRead depth) forget).mpr
  apply SourceConditionalMergeLoss.gap_positive_of_collision
    (runtimeAt (depth + 1)) (fineRead depth) forget
    (SourceWordEvenBirth.actorZero depth) (SourceWordEvenBirth.actorOne depth)
  · rfl
  · exact fine_diff depth odd

def freshCode (depth : Nat) :
    SourceWordMinimalCode.WordImage (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth) → ZMod 2 :=
  fun code => SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
    (SourceWordEvenBirth.newWord depth)
    ((SourceWordMinimalCode.wordEquiv (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth)).symm code)

theorem freshCode_query_zero (depth : Nat) (odd : Odd depth)
    (actor : Actors (runtimeAt (depth + 1))) :
    SourceWordCodeRisk.query (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth) (freshCode depth) actor = 0 := by
  simpa only [SourceWordCodeRisk.query, freshCode, Equiv.symm_apply_apply]
    using new_query_zero depth odd actor

def oldBest (depth : Nat) : ZMod 2 → SourceJointClockGraph.Carrier :=
  SourceWordFieldCode.gFineMean (runtimeAt (depth + 1))
    (SourceWordEvenBirth.oldWord depth) (fineRead depth)

def freshBest (depth : Nat) : ZMod 2 → SourceJointClockGraph.Carrier :=
  SourceWordFieldCode.gCoarseMean (runtimeAt (depth + 1))
    (SourceWordEvenBirth.oldWord depth) (fineRead depth) forget

theorem old_risk_eq (depth : Nat) :
    SourceWordCodeRisk.risk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth)
      (SourceWordObservedCode.encodeObserved (runtimeAt (depth + 1))
        (SourceWordEvenBirth.oldWord depth)) (oldBest depth) =
    SourceWordFieldCode.gRisk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth) (fineRead depth)
      (oldBest depth) := by
  apply SourceWordPersistentRecoveryGain.bit_risk_eq_gRisk_of_query_eq
  intro actor
  rw [SourceWordObservedCode.query_actual]
  rfl

theorem fresh_risk_eq (depth : Nat) (odd : Odd depth) :
    SourceWordCodeRisk.risk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth) (freshCode depth)
      (freshBest depth) =
    SourceWordFieldCode.gRisk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth) (forget ∘ fineRead depth)
      (freshBest depth) := by
  apply SourceWordPersistentRecoveryGain.bit_risk_eq_gRisk_of_query_eq
  intro actor
  rw [freshCode_query_zero depth odd actor]
  rfl

theorem exact_erasure_gain (depth : Nat) (odd : Odd depth) :
    SourceWordCodeRisk.risk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth) (freshCode depth)
      (freshBest depth) =
    SourceWordCodeRisk.risk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth)
      (SourceWordObservedCode.encodeObserved (runtimeAt (depth + 1))
        (SourceWordEvenBirth.oldWord depth)) (oldBest depth) +
    SourceWordFieldCode.gGap (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth) (fineRead depth) forget := by
  rw [fresh_risk_eq depth odd, old_risk_eq depth]
  exact SourceWordFieldCode.gRisk_refinement
    (runtimeAt (depth + 1)) (SourceWordEvenBirth.oldWord depth)
    (fineRead depth) forget

theorem strict_erasure_gain (depth : Nat) (odd : Odd depth) :
    SourceWordCodeRisk.risk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth)
      (SourceWordObservedCode.encodeObserved (runtimeAt (depth + 1))
        (SourceWordEvenBirth.oldWord depth)) (oldBest depth) <
    SourceWordCodeRisk.risk (runtimeAt (depth + 1))
      (SourceWordEvenBirth.oldWord depth) (freshCode depth)
      (freshBest depth) := by
  rw [exact_erasure_gain depth odd]
  exact lt_add_of_pos_right _ (gain_pos depth odd)

end
end SourceWordOddBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
