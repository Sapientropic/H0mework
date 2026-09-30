import H0mework.Versions.X.Fock.ReceivedStep.ActionNative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

def comparisonResidual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (nonunit : index.val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) (index.val + 1))
    (read : Nat → Key) (key : Key) : SourceJointClockGraph.Carrier :=
  let actual : ℂ := ((((receiveState (inventoryBound runtime) index.val nonunit received key).1 + 1 : Nat) : ℚ)⁻¹ : ℂ)
  let original : ℂ := ((((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).1 + 1 : Nat) : ℚ)⁻¹ : ℂ)
  let old := completeValue runtime index 0 (SourceRationalWindowReadout.decode (inventoryBound runtime) index.val (received key))
  if key = read runtime.tick.next.state then
    (1 - actual) • (old - SourceConditionalNativePosterior.decoder runtime read key) +
      (actual - original) • (SourceConditionalInventory.born (inventoryBound runtime) - SourceConditionalNativePosterior.decoder runtime read key)
  else old - SourceConditionalNativePosterior.decoder runtime read key

theorem residual_equation (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (nonunit : index.val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) (index.val + 1)) (read : Nat → Key) (key : Key) :
    completeUpdatedValue runtime index nonunit received (read runtime.tick.next.state) key -
      SourceConditionalNativePosterior.decoder runtime.tick.next read key = comparisonResidual runtime index nonunit received read key := by
  have receipt := congrArg read ((inventory_bound runtime.tick.next).symm.trans (SourceActualImageStep.next_bound runtime))
  rw [completeUpdatedValue, next_value_source, SourceConditionalNativeBirth.decoder_next, comparisonResidual, receipt]
  simp only [decide_eq_true_eq]
  split_ifs <;> module

theorem conditional_error (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (nonunit : index.val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) (index.val + 1)) (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (fun actor : Actors runtime.tick.next => read actor.val)).support) :
    (∑ actor : Actors runtime.tick.next, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime.tick.next) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime.tick.next (nextRead runtime.tick.next actor) -
        completeUpdatedValue runtime index nonunit received (read runtime.tick.next.state) key‖ ^ 2) =
      (∑ actor : Actors runtime.tick.next, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime.tick.next) key).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime.tick.next (nextRead runtime.tick.next actor) -
          SourceConditionalNativePosterior.decoder runtime.tick.next read key‖ ^ 2) +
        ‖comparisonResidual runtime index nonunit received read key‖ ^ 2 := by
  rw [SourceConditionalNativePosterior.error_decomposition runtime.tick.next read key supported,
    norm_sub_rev (SourceConditionalNativePosterior.decoder runtime.tick.next read key), residual_equation]

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
