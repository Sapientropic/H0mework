import H0mework.Fock.InverseOptimal.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionOptimal

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem field_cost (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support)
    (candidate : SourceJointClockGraph.Carrier) :
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - SourceCompiledGWord.effect depth word candidate‖ ^ 2) =
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalNativeKeys.observed depth key)‖ ^ 2) +
    ((∑ actor : Actors runtime, ‖(((SourceInverseDistributionAction.generate (fun index : Nat => (index : ZMod 2))
      (word.map SourceCopyNativeWord.encode) (inventoryBound runtime) key).2 actor).2 : ℂ)‖ ^ 2) +
      ‖SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word
        (SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) key) - candidate)‖ ^ 2) := by
  have paid := SourceConditionalNativePosterior.field_error runtime depth key supported (SourceCompiledGWord.effect depth word candidate)
  rw [SourceConditionalNativePosterior.parity_decoder, error_decomposition,
    SourceInverseDistributionLoss.generated_residual_norm] at paid
  rw [SourceConditionalNativePosterior.parity_decoder]
  exact paid

theorem field_optimal (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support)
    (candidate : SourceJointClockGraph.Carrier) :
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - SourceCompiledGWord.effect depth word
        (SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) key))‖ ^ 2) ≤
    ∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - SourceCompiledGWord.effect depth word candidate‖ ^ 2 := by
  have best := SourceConditionalNativePosterior.field_error runtime depth key supported
    (SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word
      (SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) key)))
  have other := SourceConditionalNativePosterior.field_error runtime depth key supported (SourceCompiledGWord.effect depth word candidate)
  rw [best, other, SourceConditionalNativePosterior.parity_decoder]
  exact add_le_add le_rfl (optimal depth word _ candidate)

theorem field_unique (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support)
    (candidate : SourceJointClockGraph.Carrier) :
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - SourceCompiledGWord.effect depth word candidate‖ ^ 2) =
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - SourceCompiledGWord.effect depth word
        (SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) key))‖ ^ 2) ↔
      candidate = SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) key) := by
  have best := SourceConditionalNativePosterior.field_error runtime depth key supported
    (SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word
      (SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) key)))
  have other := SourceConditionalNativePosterior.field_error runtime depth key supported (SourceCompiledGWord.effect depth word candidate)
  rw [other, best, add_left_cancel_iff, SourceConditionalNativePosterior.parity_decoder]
  exact optimal_unique depth word _ candidate

end
end SourceInverseDistributionOptimal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
