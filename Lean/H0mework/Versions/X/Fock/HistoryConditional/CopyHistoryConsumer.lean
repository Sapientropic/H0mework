import H0mework.Versions.X.Fock.HistoryConditional.CopyHistoryRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeHistory

open SourcePrimeHistoryRecovery SourceGeneratedActionObservationHistory
open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem dynamic_model_fibre (bound : Nat) (left right : Fin (bound + 1)) :
    read bound left.val = read bound right.val ↔
      projection nativeAction observation (SourceOperationNative.statePoint process (left.val + 1)) =
        projection nativeAction observation (SourceOperationNative.statePoint process (right.val + 1)) := by
  rw [original_model_fibre sourceOwner, (SourceOperationNative.statePoint_injective process).eq_iff,
    Nat.add_left_inj]
  exact ⟨fun same => congrArg Fin.val (read_injective bound same),
    fun same => congrArg (read bound) same⟩

theorem original_transfer (bound : Nat) (task : Fin (bound + 1) → ℂ) (actor : Fin (bound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField runtimeSeed bound
      (SourceWeightedRecovery.Runtime.Actor.actorTransfer (process := process) rawField runtimeSeed bound
        (SourceWeightedRecovery.taskValue (historyPMF bound) task))
      (SourceConditionalTransfer.nextAtom (process := process) rawField runtimeSeed bound actor) =
    ∑ candidate : Fin (bound + 1),
      ((SourceConditionalNativeObservers.generate (read bound) bound (read bound actor.val)).2 candidate : ℂ) • task candidate := by
  rw [complete_recovers sourceOwner, native_row]
  classical
  rw [Finset.sum_eq_single actor]
  · simp
  · intro other _ different
    simp only [if_neg different, Rat.cast_zero, zero_smul]
  · intro absent
    exact (absent (Finset.mem_univ actor)).elim

theorem history_material (bound : Nat) (actor : Fin (bound + 1))
    (time : Fin (windowBound sourceOwner bound + 1)) :
    SourceCopyNativeKeys.key (actor.val + 1 + time.val) =
      SourceCopyNativeKeys.key
        (((history runtimeSeed (completionDepth sourceOwner bound)).stageAt (cell sourceOwner bound actor time)).next.state) ∧
      type_of% (sample_factorizes runtimeSeed (completionDepth sourceOwner bound) (cell sourceOwner bound actor time)) := by
  refine ⟨?_, sample_factorizes runtimeSeed (completionDepth sourceOwner bound) (cell sourceOwner bound actor time)⟩
  apply (SourceCopyNativeKeys.key_fibre _ _).mpr
  exact (query_value sourceOwner bound actor time).symm.trans (query_is_material sourceOwner bound actor time)

end
end SourceCopyNativeHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
