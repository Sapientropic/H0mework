import H0mework.Fock.HistoryConditional.MergeLossKernel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalMergeLoss

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead dynamicRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def forgetAll (_value : ZMod 2) : Unit := ()

def collapse (runtime : LivingRuntimeState process) : SourceJointClockGraph.Carrier :=
  decoder runtime (fun index : Nat => (index : ZMod 2)) forgetAll ()

theorem fine_field (runtime : LivingRuntimeState process) (depth : Nat) (actor : Actors runtime) :
    SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) (actor.val : ZMod 2) =
      SourceConditionalNativeKeys.decoder runtime depth (dynamicRead runtime depth actor) := by
  have observed := SourceConditionalNativeKeys.source_observed (inventoryBound runtime) depth actor
  rw [SourceConditionalInventory.observation_original] at observed
  rw [observed, SourceConditionalNativePosterior.parity_decoder]

theorem parity_loss (runtime : LivingRuntimeState process) (depth : Nat) :
    (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - collapse runtime‖ ^ 2) =
      SourceConditionalVector.dynamicError runtime depth (SourceConditionalNativeKeys.decoder runtime depth) +
        gap runtime (fun index : Nat => (index : ZMod 2)) forgetAll := by
  have paid := loss runtime (fun index : Nat => (index : ZMod 2)) forgetAll
  simp only [fine_field runtime depth, forgetAll] at paid
  simp only [collapse, gap, fine_field runtime depth, forgetAll, SourceConditionalVector.dynamicError]
  with_reducible exact paid

theorem parity_gap_positive (runtime : LivingRuntimeState process) (enough : 1 ≤ inventoryBound runtime) :
    0 < gap runtime (fun index : Nat => (index : ZMod 2)) forgetAll := by
  let one : Actors runtime := ⟨1, by omega⟩
  apply gap_positive_of_collision runtime (fun index : Nat => (index : ZMod 2)) forgetAll 0 one rfl
  change (0 : ZMod 2) ≠ 1
  decide

theorem parity_strict (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) (depth : Nat) :
    0 < SourceConditionalVector.dynamicError runtime depth (SourceConditionalNativeKeys.decoder runtime depth) ∧
    SourceConditionalVector.dynamicError runtime depth (SourceConditionalNativeKeys.decoder runtime depth) <
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - collapse runtime‖ ^ 2 := by
  have lower := SourceConditionalVector.dynamic_error_lower runtime enough depth (SourceConditionalNativeKeys.decoder runtime depth)
  have first : 0 < (3 : ℝ) / (inventoryBound runtime + 1) := by positivity
  refine ⟨first.trans_le lower, ?_⟩
  rw [parity_loss]
  exact lt_add_of_pos_right _ (parity_gap_positive runtime (by omega))

theorem parity_update (bound : Nat) :
    SourceConditionalNativeMerge.merge (fun index : Nat => (index : ZMod 2)) forgetAll (bound + 1)
      (SourceConditionalNativeKeys.advance bound (SourceConditionalNativeKeys.generate bound)) =
      SourceConditionalNativeObservers.advance (forgetAll ∘ (fun index : Nat => (index : ZMod 2))) bound
        (SourceConditionalNativeMerge.merge (fun index : Nat => (index : ZMod 2)) forgetAll bound
          (SourceConditionalNativeKeys.generate bound)) :=
  SourceConditionalNativeMerge.merge_next (fun index : Nat => (index : ZMod 2)) forgetAll bound

end
end SourceConditionalMergeLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
