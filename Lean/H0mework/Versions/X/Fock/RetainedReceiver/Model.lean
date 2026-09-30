import H0mework.Versions.X.Fock.RetainedReceiver.Trajectory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*} [DecidableEq Key]
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors NextModel nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def model (runtime : LivingRuntimeState process) (frame : At runtime Key) (key : Key) : NextModel runtime :=
  ∑ actor : Actors runtime, ((frame.native key).2 actor : ℂ) • nextRead runtime actor

def observed (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (frame : At runtime Key) (key : Key) : NextModel runtime :=
  SourceWindowPosterior.model runtime nonunit (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0
    (SourceReceivedConditionalStep.completeSamples (inventoryBound runtime) (maximumIndex runtime).val
      (rawAt (inventoryBound runtime) (maximumIndex runtime).val frame key)))

def residual (runtime : LivingRuntimeState process) (frame : At runtime Key) (key : Key) : SourceJointClockGraph.Carrier :=
  value runtime frame key - SourceConditionalVector.realizeModel runtime (model runtime frame key)

theorem model_source (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key) (key : Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) :
    model runtime frame key = SourceConditionalNativePosterior.model runtime read key := by
  rw [model, source]
  rfl

theorem observed_realization (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (frame : At runtime Key) (key : Key) :
    SourceConditionalVector.realizeModel runtime (observed runtime nonunit frame key) = value runtime frame key := by
  have decoded := SourceReceivedConditionalStep.complete_roundtrip runtime (maximumIndex runtime) nonunit 0
    (rawAt (inventoryBound runtime) (maximumIndex runtime).val frame key)
  simp only [Nat.add_zero] at decoded
  have paid := SourceRationalWindowReadout.decoded_model runtime nonunit
    (SourceReceivedConditionalStep.completeSamples (inventoryBound runtime) (maximumIndex runtime).val
      (rawAt (inventoryBound runtime) (maximumIndex runtime).val frame key))
  change SourceReceivedConditionalStep.completeValue runtime (maximumIndex runtime) 0
    (SourceRationalWindowReadout.decode (inventoryBound runtime) (maximumIndex runtime).val
      (SourceReceivedConditionalStep.completeSamples (inventoryBound runtime) (maximumIndex runtime).val
        (rawAt (inventoryBound runtime) (maximumIndex runtime).val frame key))) = _ at paid
  rw [decoded] at paid
  exact paid.symm

theorem reconstruction (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (frame : At runtime Key) (key : Key) :
    SourceConditionalVector.realizeModel runtime (model runtime frame key) + residual runtime frame key =
      SourceConditionalVector.realizeModel runtime (observed runtime nonunit frame key) := by
  rw [observed_realization, residual]
  abel

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
