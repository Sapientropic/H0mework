import H0mework.Versions.X.Fock.HistoryConditional.NativePosteriorModel
import H0mework.Versions.X.Fock.HistoryConditional.NativeObserversRows

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeObservers

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors NextModel nextRead fullRead full_supported)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem clock_posterior (runtime : LivingRuntimeState process) (actor candidate : Actors runtime) :
    ((generate (clockRead 0) (inventoryBound runtime) (fullRead runtime actor)).2 candidate : ℝ) =
      (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (fullRead runtime)
        (fullRead runtime actor) (full_supported runtime actor) candidate).toReal := by
  have same : (fun index : Actors runtime => clockRead 0 index.val) = fullRead runtime :=
    funext (fun index => (full_source runtime index).symm)
  have native := SourceConditionalNativePosterior.posterior (clockRead 0) (inventoryBound runtime)
    (fullRead runtime actor) (by rw [same]; exact full_supported runtime actor) candidate
  simpa only [same] using native

def model (runtime : LivingRuntimeState process) (value : ℤ × ℤ) : NextModel runtime :=
  SourceConditionalNativePosterior.model runtime (clockRead 0) value

def decoder (runtime : LivingRuntimeState process) (value : ℤ × ℤ) : SourceJointClockGraph.Carrier :=
  SourceConditionalVector.realizeModel runtime (model runtime value)

theorem model_original (runtime : LivingRuntimeState process) (actor : Actors runtime) :
    model runtime (fullRead runtime actor) =
      SourceConditionalModel.modelEstimate runtime (fullRead runtime actor) (full_supported runtime actor) := by
  rw [model, SourceConditionalNativePosterior.model, SourceConditionalModel.modelEstimate]
  apply Finset.sum_congr rfl
  intro candidate _
  have weight : ((generate (clockRead 0) (inventoryBound runtime) (fullRead runtime actor)).2 candidate : ℂ) =
      ((SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (fullRead runtime)
        (fullRead runtime actor) (full_supported runtime actor) candidate).toReal : ℂ) := by
    exact_mod_cast clock_posterior runtime actor candidate
  rw [weight]

theorem model_recovers (runtime : LivingRuntimeState process) (actor : Actors runtime) :
    model runtime (fullRead runtime actor) = nextRead runtime actor := by
  rw [model_original, SourceConditionalModel.model_recovers]

theorem decoder_recovers (runtime : LivingRuntimeState process) (actor : Actors runtime) :
    decoder runtime (fullRead runtime actor) =
      SourceCopyNativeModelStep.sourceValue ((history runtimeSeed (inventoryBound runtime)).stageAt actor).next := by
  rw [decoder, model_original, ← SourceConditionalVector.full_clock_original]
  exact SourceConditionalVector.full_recovers runtime actor

theorem error_zero (runtime : LivingRuntimeState process) :
    (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - decoder runtime (fullRead runtime actor)‖ ^ 2) = 0 := by
  simp only [decoder, model_recovers, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero]

def updated (runtime : LivingRuntimeState process) : State (ℤ × ℤ) (inventoryBound runtime.tick.next) :=
  (SourceActualImageStep.next_bound runtime).symm ▸
    advance (clockRead 0) (inventoryBound runtime) (generate (clockRead 0) (inventoryBound runtime))

theorem state_next (runtime : LivingRuntimeState process) :
    generate (clockRead 0) (inventoryBound runtime.tick.next) = updated runtime := by
  rw [updated, ← generated_next]
  have transport (left right : Nat) (same : left = right) :
      (same ▸ generate (clockRead 0) left) = generate (clockRead 0) right := by
    cases same
    rfl
  exact (transport _ _ (SourceActualImageStep.next_bound runtime).symm).symm

theorem next_recovers (runtime : LivingRuntimeState process) (actor : Actors runtime.tick.next) :
    SourceConditionalVector.realizeModel runtime.tick.next
      (∑ candidate : Actors runtime.tick.next,
        ((updated runtime (fullRead runtime.tick.next actor)).2 candidate : ℂ) • nextRead runtime.tick.next candidate) =
      SourceCopyNativeModelStep.sourceValue ((history runtimeSeed (inventoryBound runtime.tick.next)).stageAt actor).next := by
  rw [← state_next]
  exact decoder_recovers runtime.tick.next actor

end
end SourceConditionalNativeObservers
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
