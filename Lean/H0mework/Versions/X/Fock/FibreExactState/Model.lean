import H0mework.Versions.X.Fock.FibreExactState.Recovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFibreExactState

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors NextModel nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def model (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) : NextModel runtime :=
  ∑ actor : Actors runtime,
    ((restore (inventoryBound runtime) (maximumIndex runtime).val nonunit samples).2 actor : ℂ) • nextRead runtime actor

def observed (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) : NextModel runtime :=
  SourceWindowPosterior.model runtime nonunit (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples)

def residual (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) : SourceJointClockGraph.Carrier :=
  SourceConditionalVector.realizeModel runtime (observed runtime nonunit samples) -
    SourceConditionalVector.realizeModel runtime (model runtime nonunit samples)

theorem reconstruction (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) :
    SourceConditionalVector.realizeModel runtime (model runtime nonunit samples) + residual runtime nonunit samples =
      SourceConditionalVector.realizeModel runtime (observed runtime nonunit samples) := by
  rw [residual]
  abel

theorem model_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    {Key : Type*} [DecidableEq Key] (read : Nat → Key) (key : Key)
    (budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    model runtime nonunit samples = SourceConditionalNativePosterior.model runtime read key := by
  rw [model, restored_source runtime nonunit samples read key budget]
  rfl

theorem residual_bound (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    {Key : Type*} [DecidableEq Key] (read : Nat → Key) (key : Key)
    (budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    ‖residual runtime nonunit samples‖ ^ 2 ≤
      SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
        SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
          (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples -
            SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
              (SourceConditionalNativePosterior.decoder runtime read key)) := by
  have source := SourceWindowPosterior.bias_bound runtime nonunit read key
    (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples)
  rw [SourceWindowPosterior.decoder_tail_zero runtime nonunit read key, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at source
  have identity : residual runtime nonunit samples =
      SourceConditionalVector.realizeModel runtime
        (SourceWindowPosterior.model runtime nonunit
          (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples)) -
        SourceConditionalNativePosterior.decoder runtime read key := by
    unfold residual
    rw [model_source runtime nonunit samples read key budget]
    rfl
  rw [identity]
  exact source

end
end SourceFibreExactState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
