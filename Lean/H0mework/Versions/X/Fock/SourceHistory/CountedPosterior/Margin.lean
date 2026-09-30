import H0mework.Versions.X.Fock.SourceHistory.CountedObservation.Complete

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedPosterior

open SourceRetainedReceiver (At next residual trajectory)
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem counted_residual_next (runtime : LivingRuntimeState process) (frame : At runtime Key)
    (read : Nat → Key) (key : Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) :
    (((next runtime frame (read runtime.tick.next.state)).native key).1 : ℂ) •
      residual runtime.tick.next (next runtime frame (read runtime.tick.next.state)) key =
        ((frame.native key).1 : ℂ) • residual runtime frame key := by
  rw [SourceRetainedCoarsening.next_count, SourceRetainedReceiver.residual_next runtime frame read key source]
  by_cases selected : key = read runtime.tick.next.state
  · simp only [if_pos selected, smul_smul, SourceStableReceivedCount.contraction, Rat.cast_div, Rat.cast_natCast]
    congr 1
    have nonzero : (((frame.native key).1 + 1 : Nat) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    field_simp
  · simp only [if_neg selected]

theorem counted_trajectory (runtime : LivingRuntimeState process) (initial : At runtime Key)
    (read : Nat → Key) (key : Key)
    (source : initial.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) (steps : Nat) :
    (((trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps).native key).1 : ℂ) •
      residual (runtime.advance steps)
        (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps) key =
          ((initial.native key).1 : ℂ) • residual runtime initial key := by
  induction steps with
  | zero => simp only [SourceRetainedReceiver.trajectory_zero, LivingRuntimeState.advance]
  | succ steps previous =>
    rw [SourceRetainedReceiver.trajectory_next]
    simp only [LivingRuntimeState.advance]
    rw [SourceRetainedReceiver.receipt_at runtime read steps,
      counted_residual_next (runtime.advance steps) _ read key
        (SourceRetainedReceiver.trajectory_native runtime initial read source steps)]
    exact previous

private theorem counted_small (runtime : LivingRuntimeState process) (frame : At runtime Key)
    (read : Nat → Key) (key : Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (small : ‖residual runtime frame key‖ < SourcePosteriorStability.threshold runtime) :
    ‖((frame.native key).1 : ℂ) • residual runtime frame key‖ < 1 / 2 := by
  have count_le : (frame.native key).1 ≤ inventoryBound runtime + 1 := by
    rw [source, SourceConditionalNativePosterior.count_fibre]
    simpa only [Fintype.card_fin] using
      (Finset.card_le_univ (SourceUniformFibreVariance.fibre (inventoryBound runtime) (fun actor => read actor.val) key))
  rw [norm_smul, Complex.norm_natCast]
  calc
    ((frame.native key).1 : ℝ) * ‖residual runtime frame key‖ ≤
        (inventoryBound runtime + 1 : ℝ) * ‖residual runtime frame key‖ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast count_le) (norm_nonneg _)
    _ < (inventoryBound runtime + 1 : ℝ) * SourcePosteriorStability.threshold runtime :=
      mul_lt_mul_of_pos_left small (by positivity)
    _ = 1 / 2 := by
      rw [SourcePosteriorStability.threshold]
      have nonzero : (inventoryBound runtime + 1 : ℝ) ≠ 0 := by positivity
      field_simp

theorem initial_half_margin (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2)
    (key : Key) :
    let initial := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
    ‖((initial.native key).1 : ℂ) • residual runtime initial key‖ < 1 / 2 := by
  dsimp only
  let initial : At runtime Key := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
  have native := SourceRetainedReceiver.start_native runtime nonunit read samples budgets
  have estimate := SourceRetainedReceiver.start_bound runtime nonunit read samples key budgets
  have strict := lt_of_le_of_lt estimate
    (SourceReceivedKeyInventory.extended_budgets runtime nonunit read samples budgets key)
  have squared : ‖residual runtime initial key‖ ^ 2 < SourcePosteriorStability.threshold runtime ^ 2 := by
    with_reducible exact strict
  have positive := SourcePosteriorStability.threshold_positive runtime
  have small : ‖residual runtime initial key‖ < SourcePosteriorStability.threshold runtime := by
    nlinarith [norm_nonneg (residual runtime initial key)]
  with_reducible exact counted_small runtime initial read key native small


theorem trajectory_half_margin (runtime : LivingRuntimeState process) (initial : At runtime Key)
    (read : Nat → Key) (key : Key)
    (source : initial.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (paid : ‖((initial.native key).1 : ℂ) • residual runtime initial key‖ < 1 / 2) (steps : Nat) :
    ‖(((trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps).native key).1 : ℂ) •
      residual (runtime.advance steps)
        (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps) key‖ < 1 / 2 := by
  rw [counted_trajectory runtime initial read key source steps]
  exact paid

end
end SourceCountedPosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
