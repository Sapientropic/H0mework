import H0mework.Versions.X.Fock.SourceHistory.CountedPosterior.Coordinate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedPosterior

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors NextModel nextRead)
open SourceRetainedReceiver (At)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem restored_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table Key) (frame : At runtime Key) (read : Nat → Key) (key : Key)
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (smallHalf : ‖((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key‖ < 1 / 2) :
    restore (inventoryBound runtime) (maximumIndex runtime).val nonunit table key =
      SourceConditionalNativeObservers.generate read (inventoryBound runtime) key := by
  have identified :
      Finset.univ.filter (fun actor : Actors runtime =>
        (1 / 2 : ℚ) < SourceCountedObservation.coordinate (SourceCountedObservation.lookup table key).hilbert (actor.val + 1)) =
      SourceUniformFibreVariance.fibre (inventoryBound runtime) (fun actor => read actor.val) key := by
    ext actor
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SourceUniformFibreVariance.fibre_mem]
    have coordinateSmall := (SourcePosteriorStability.coordinate_norm (actor.val + 1)
      (((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key)).trans_lt smallHalf
    rw [← counted_residual_coordinate runtime table frame read key actor source native] at coordinateSmall
    have realSmall := (Complex.abs_re_le_norm _).trans_lt coordinateSmall
    by_cases present : read actor.val = key
    · simp only [if_pos present, Complex.sub_re, Complex.ratCast_re, Complex.one_re] at realSmall
      have lower := (abs_lt.mp realSmall).1
      have aboveReal : (1 / 2 : ℝ) <
          (SourceCountedObservation.coordinate (SourceCountedObservation.lookup table key).hilbert (actor.val + 1) : ℝ) := by
        linarith
      have above : (1 / 2 : ℚ) <
          SourceCountedObservation.coordinate (SourceCountedObservation.lookup table key).hilbert (actor.val + 1) := by
        apply (Rat.cast_lt (K := ℝ)).mp
        simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using aboveReal
      exact iff_of_true above present
    · simp only [if_neg present, sub_zero, Complex.ratCast_re] at realSmall
      have below : SourceCountedObservation.coordinate (SourceCountedObservation.lookup table key).hilbert (actor.val + 1) <
          (1 / 2 : ℚ) := by
        apply (Rat.cast_lt (K := ℝ)).mp
        simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (abs_lt.mp realSmall).2
      exact iff_of_false (not_lt.mpr below.le) present
  simp only [restore_formula runtime (maximumIndex runtime) nonunit table key, identified]
  apply Prod.ext
  · exact (SourceConditionalNativePosterior.count_fibre read (inventoryBound runtime) key).symm
  · funext actor
    rw [SourceConditionalNativePosterior.weight_fibre, ← SourceConditionalNativePosterior.count_fibre]
    simp only [SourceUniformFibreVariance.fibre_mem]

def model (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table Key) (key : Key) : NextModel runtime :=
  let entry := SourceCountedObservation.lookup table key
  SourceFibreExactState.model runtime nonunit
    (SourceReceivedConditionalStep.completeSamples (inventoryBound runtime) (maximumIndex runtime).val
      ((fun position => SourceCountedObservation.coordinate entry.hilbert position.val / (inventoryBound runtime + 1 : Nat)),
        entry.mass / (inventoryBound runtime + 1 : Nat), entry.clock / (inventoryBound runtime + 1 : Nat)))

theorem model_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table Key) (frame : At runtime Key) (read : Nat → Key) (key : Key)
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (smallHalf : ‖((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key‖ < 1 / 2) :
    model runtime nonunit table key = SourceConditionalNativePosterior.model runtime read key := by
  unfold model SourceFibreExactState.model
  change (∑ actor : Actors runtime,
    ((restore (inventoryBound runtime) (maximumIndex runtime).val nonunit table key).2 actor : ℂ) • nextRead runtime actor) = _
  rw [restored_source runtime nonunit table frame read key source native smallHalf]
  rfl

end
end SourceCountedPosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
