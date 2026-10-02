import H0mework.Versions.R2.Probability.Runtime.History
import H0mework.Versions.R2.Realization.Operations.RuntimeSuccessor

/-! The joint law uses one history index for both ends of its actual transition. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedRuntimeHistoryProbability

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}

def nextSample (runtime : LivingRuntimeState process) (bound : Nat)
    (index : Fin (bound + 1)) : process.State :=
  ((history runtime bound).stageAt index).next.state

@[simp] theorem nextSample_eq_successor (runtime : LivingRuntimeState process) (bound : Nat)
    (index : Fin (bound + 1)) :
    nextSample runtime bound index = process.successor (sample runtime bound index) := rfl

theorem nextSample_eq_shift (runtime : LivingRuntimeState process) (bound : Nat)
    (index : Fin (bound + 1)) :
    nextSample runtime bound index = sample runtime.tick.next bound index := by
  change (runtime.advance (index.val + 1)).state =
    (runtime.tick.next.advance index.val).state
  rw [SourceOperationRuntime.runtime_tail]

def jointPMF (runtime : LivingRuntimeState process) (bound : Nat) :
    PMF (process.State × process.State) :=
  (historyPMF bound).map fun index =>
    (sample runtime bound index, nextSample runtime bound index)

theorem joint_fst (runtime : LivingRuntimeState process) (bound : Nat) :
    (jointPMF runtime bound).map Prod.fst = statePMF runtime bound := by
  rw [jointPMF, PMF.map_comp]
  rfl

theorem joint_snd (runtime : LivingRuntimeState process) (bound : Nat) :
    (jointPMF runtime bound).map Prod.snd = statePMF runtime.tick.next bound := by
  rw [jointPMF, PMF.map_comp]
  simp only [Function.comp_def, nextSample_eq_shift]
  rfl

theorem statePMF_successor (runtime : LivingRuntimeState process) (bound : Nat) :
    (statePMF runtime bound).map process.successor = statePMF runtime.tick.next bound := by
  rw [statePMF, PMF.map_comp]
  simp only [Function.comp_def, ← nextSample_eq_successor, nextSample_eq_shift]
  rfl

theorem joint_support_iff (runtime : LivingRuntimeState process) (bound : Nat)
    (value : process.State × process.State) :
    value ∈ (jointPMF runtime bound).support ↔
      ∃ index : Fin (bound + 1),
        (sample runtime bound index, nextSample runtime bound index) = value := by
  rw [jointPMF, PMF.mem_support_map_iff]
  simp only [historyPMF, PMF.mem_support_uniformOfFintype, true_and]

theorem joint_support_successor (runtime : LivingRuntimeState process) (bound : Nat)
    (value : process.State × process.State) (mem : value ∈ (jointPMF runtime bound).support) :
    value.2 = process.successor value.1 := by
  obtain ⟨index, rfl⟩ := (joint_support_iff runtime bound value).mp mem
  exact nextSample_eq_successor runtime bound index

end
end SourceGeneratedRuntimeHistoryProbability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
