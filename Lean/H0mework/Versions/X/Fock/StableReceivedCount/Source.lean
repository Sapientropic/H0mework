import H0mework.Versions.X.Fock.ReceivedStep.Material

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceStableReceivedCount

def threshold (bound : Nat) : ℚ := 1 / (2 * ((bound + 1 : Nat) : ℚ))

def support (bound stride : Nat) (nonunit : stride ≠ 0)
    (samples : SourceRationalWindowReadout.Samples bound (stride + 1)) : Finset (Fin (bound + 1)) :=
  Finset.univ.filter (fun actor => threshold bound < SourceRationalWindowReadout.recover bound stride nonunit samples actor)

def count (bound stride : Nat) (nonunit : stride ≠ 0)
    (samples : SourceRationalWindowReadout.Samples bound (stride + 1)) : Nat :=
  (support bound stride nonunit samples).card

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem threshold_source (runtime : LivingRuntimeState process) :
    (threshold (inventoryBound runtime) : ℝ) = SourcePosteriorStability.threshold runtime := by
  simp [threshold, SourcePosteriorStability.threshold]

theorem model_coordinate (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (actor : Actors runtime) :
    SourceGInformationCost.coordinateRead (actor.val + 1)
      (SourceConditionalVector.realizeModel runtime
        (SourceWindowPosterior.model runtime nonunit (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples))) =
      (SourceRationalWindowReadout.recover (inventoryBound runtime) (maximumIndex runtime).val nonunit samples actor : ℂ) := by
  have original := congrArg (SourceGInformationCost.coordinateRead (actor.val + 1))
    (SourceRationalWindowReadout.decoded_model runtime nonunit samples)
  have coordinate := SourceCopyCurrentCoordinates.hilbert_lift_at runtime (maximumIndex runtime) 0
    (SourceRationalWindowReadout.coordinates runtime (maximumIndex runtime) 0
      (SourceRationalWindowReadout.decode (inventoryBound runtime) (maximumIndex runtime).val samples)).1
    (SourceRationalWindowReadout.weightCoordinate runtime (maximumIndex runtime) nonunit actor)
  exact original.symm.trans coordinate

theorem read_weight_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (actor : Actors runtime) :
    (SourcePosteriorReadback.readWeight runtime
      (SourceWindowPosterior.model runtime nonunit (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples)) actor).toReal =
      max (SourceRationalWindowReadout.recover (inventoryBound runtime) (maximumIndex runtime).val nonunit samples actor : ℝ) 0 := by
  rw [SourcePosteriorReadback.readWeight, model_coordinate, ENNReal.toReal_ofReal']
  simp

end
end SourceStableReceivedCount
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
