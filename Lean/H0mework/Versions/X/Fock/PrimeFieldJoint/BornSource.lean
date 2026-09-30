import H0mework.Versions.X.Fock.PrimeFieldJoint.CofinalConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedBornDecoder

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedJointTime SourceGeneratedJointClockGraph
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAtomicObservation SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def coordinate (index : Nat) : SourceJointClockGraph.Carrier →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : Nat => ℂ) 2 index).comp (SourceMassCompletion.firstRead.comp SourceJointClockGraph.joint)

def target (runtime : LivingRuntimeState process) (depth : Nat) : SourceJointClockGraph.Carrier :=
  nextFieldRead depth (inventoryBound (next runtime))
    (timeTransfer depth (inventoryBound (next runtime)) (newest runtime depth))

theorem target_source (runtime : LivingRuntimeState process) (depth : Nat) :
    target runtime depth = SourceJointClockGraph.action
      (SourceJointClockGraph.read (word depth (inventoryBound (next runtime)) (newest runtime depth))) :=
  original_time_square _ _ _

theorem coordinate_action_word (index : Nat) (sourceWord : Nat →₀ ℂ) :
    coordinate (index + 1) (SourceJointClockGraph.action (SourceJointClockGraph.read sourceWord)) = sourceWord index := by
  rw [SourceJointClockGraph.action_source]
  change readWord (push ℂ sourceWord) (index + 1) = sourceWord index
  rw [readWord_push, SourceJointTransfer.shift_coordinate, readWord_coordinate]

theorem target_coordinate (runtime : LivingRuntimeState process) (depth : Nat) :
    coordinate (inventoryBound (next runtime) + 1) (target runtime depth) =
      (Real.sqrt (historyPMF (inventoryBound (next runtime)) (Fin.last (inventoryBound (next runtime)))).toReal : ℂ) := by
  rw [target_source, coordinate_action_word]
  change SourceHistoryWord.word (inventoryBound (next runtime))
    (Actor.currentPullback depth (inventoryBound (next runtime)) (newest runtime depth))
      (Fin.last (inventoryBound (next runtime))).val = _
  rw [newest_samples, SourceHistoryWord.word_at, SourceHistoryWord.coefficient_value,
    cotest_at _ _ (SourceUniformFibreVariance.source_positive _ _), mul_one]

theorem prior_coordinate (runtime : LivingRuntimeState process)
    (proposal : SourceJointFiniteDecoder.Space (inventoryBound runtime)) :
    coordinate (inventoryBound (next runtime) + 1) (SourceJointFiniteDecoder.action (inventoryBound runtime) proposal) = 0 := by
  change coordinate _ (SourceJointClockGraph.action (SourceJointFiniteDecoder.read _ proposal)) = 0
  rw [SourceJointFiniteDecoder.read_source, coordinate_action_word]
  exact SourceHistoryWord.word_outside _ _ _ (Nat.succ_le_of_lt (inventory_grows runtime))

theorem coordinate_norm_le (index : Nat) (value : SourceJointClockGraph.Carrier) : ‖coordinate index value‖ ≤ ‖value‖ := by
  change ‖SourceMassCompletion.firstRead (SourceJointClockGraph.joint value) index‖ ≤ ‖value‖
  exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) _ index).trans
    ((WithLp.norm_fst_le SourceOwnedObservationHistory.SourceShift.H (SourceJointClockGraph.joint value)).trans (WithLp.norm_fst_le SourceMassCompletion.Joint value))

end
end SourceGeneratedBornDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
