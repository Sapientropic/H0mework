import H0mework.Versions.X.Fock.SourceHistory.CountedObservation.Source
import H0mework.Versions.X.Fock.SourceHistory.CountedPosterior.Restore

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedPosterior

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors)
open SourceRetainedReceiver (At)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

private theorem value_coordinate (runtime : LivingRuntimeState process) (frame : At runtime Key)
    (key : Key) (position : Nat) :
    SourceGInformationCost.coordinateRead position (SourceRetainedReceiver.value runtime frame key) =
      (SourceReceivedConditionalStep.coordinateAt (inventoryBound runtime) (maximumIndex runtime).val
        (SourceRetainedReceiver.rawAt (inventoryBound runtime) (maximumIndex runtime).val frame key) position : ℂ) := by
  change SourceCopyTimeModel.hilbert (SourceRetainedReceiver.value runtime frame key) position = _
  exact (SourceReceivedConditionalStep.coordinate_source runtime (maximumIndex runtime) 0
    (SourceRetainedReceiver.rawAt (inventoryBound runtime) (maximumIndex runtime).val frame key) position).symm

omit [DecidableEq Key] in
private theorem model_coordinate (runtime : LivingRuntimeState process) (frame : At runtime Key)
    (key : Key) (actor : Actors runtime) :
    SourceGInformationCost.coordinateRead (actor.val + 1)
      (SourceConditionalVector.realizeModel runtime (SourceRetainedReceiver.model runtime frame key)) =
        ((frame.native key).2 actor : ℂ) := by
  simp only [SourceRetainedReceiver.model, map_sum, map_smul,
    ← SourceConditionalInventory.values_original runtime, SourceGInformationCost.coordinate_actual]
  rw [Finset.sum_eq_single actor]
  · simp only [ite_true, smul_eq_mul, mul_one]
  · intro other _ different
    rw [if_neg different, smul_zero]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

theorem counted_residual_coordinate (runtime : LivingRuntimeState process)
    (table : SourceCountedObservation.Table Key) (frame : At runtime Key) (read : Nat → Key)
    (key : Key) (actor : Actors runtime)
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) :
    (SourceCountedObservation.coordinate (SourceCountedObservation.lookup table key).hilbert (actor.val + 1) : ℂ) -
      (if read actor.val = key then 1 else 0) =
        SourceGInformationCost.coordinateRead (actor.val + 1)
          (((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key) := by
  have represented := congrArg (fun value : ℚ => (value : ℂ)) ((source.rows key).hilbert_eq (actor.val + 1))
  simp only [Rat.cast_mul, Rat.cast_natCast] at represented
  have indicator : ((frame.native key).1 : ℂ) * ((frame.native key).2 actor : ℂ) =
      if read actor.val = key then 1 else 0 := by
    rw [native, SourceConditionalNativePosterior.weight_fibre]
    by_cases present : read actor.val = key
    · simp only [if_pos present, Rat.cast_inv, Rat.cast_natCast]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr
        (SourceConditionalNativePosterior.count_positive read (inventoryBound runtime) key actor present).ne')
    · simp only [if_neg present, Rat.cast_zero, mul_zero]
  rw [SourceRetainedReceiver.residual, map_smul, map_sub, value_coordinate, model_coordinate]
  simp only [smul_eq_mul, mul_sub]
  rw [represented, indicator]

end
end SourceCountedPosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
