import H0mework.Fock.RetainedReceiver.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*} [DecidableEq Key]

def run (bound stride : Nat) (receipts : Nat → Key) (initial : Frame Key bound stride) :
    (steps : Nat) → Frame Key (bound + steps) (stride + steps) :=
  Nat.rec initial (fun steps current =>
    step (bound + steps) (stride + steps) (stride + steps + 1) current (receipts steps))

theorem run_native (bound stride : Nat) (initial : Frame Key bound stride) (read : Nat → Key)
    (source : initial.native = SourceConditionalNativeObservers.generate read bound) (steps : Nat) :
    (run bound stride (fun offset => read (bound + offset + 1)) initial steps).native =
      SourceConditionalNativeObservers.generate read (bound + steps) := by
  induction steps with
  | zero => exact source
  | succ steps previous =>
    change SourceConditionalNativeObservers.advance (fun _ => read (bound + steps + 1)) (bound + steps)
      (run bound stride (fun offset => read (bound + offset + 1)) initial steps).native = _
    rw [previous]
    change _ = SourceConditionalNativeObservers.generate read ((bound + steps) + 1)
    rw [SourceConditionalNativeObservers.generated_next]
    rfl

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem started_run (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat) :
    (run (inventoryBound runtime) (maximumIndex runtime).val
      (fun offset => read (inventoryBound runtime + offset + 1))
      (start (inventoryBound runtime) (maximumIndex runtime).val nonunit
        (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples) steps).native =
          SourceConditionalNativeObservers.generate read (inventoryBound runtime + steps) :=
  run_native _ _ _ read (start_native runtime nonunit read samples budgets) steps

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
