import H0mework.Versions.X.Fock.RetainedReceiver.Initial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*}
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem receipt_at (runtime : LivingRuntimeState process) (read : Nat → Key) (steps : Nat) :
    read (inventoryBound runtime + steps + 1) = read (runtime.advance steps).tick.next.state := by
  apply congrArg read
  rw [← inventory_bound (runtime.advance steps).tick.next, SourceActualImageStep.next_bound, SourceGraphRecurrence.advance_depth]

variable [DecidableEq Key]

private theorem contraction_square (members : Nat) :
    (SourceStableReceivedCount.contraction members : ℝ) ^ 2 ≤ 1 := by
  have lower : (0 : ℝ) ≤ (SourceStableReceivedCount.contraction members : ℝ) := by
    exact_mod_cast SourceStableReceivedCount.contraction_nonnegative members
  have upper : (SourceStableReceivedCount.contraction members : ℝ) < 1 := by
    exact_mod_cast SourceStableReceivedCount.contraction_lt_one members
  nlinarith

theorem trajectory_residual (runtime : LivingRuntimeState process) (initial : At runtime Key) (read : Nat → Key) (key : Key)
    (source : initial.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) (steps : Nat) :
    residual (runtime.advance (steps + 1))
      (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) (steps + 1)) key =
      if key = read (inventoryBound runtime + steps + 1) then
        (SourceStableReceivedCount.contraction
          ((trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps).native key).1 : ℂ) •
            residual (runtime.advance steps) (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps) key
      else residual (runtime.advance steps) (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps) key := by
  rw [trajectory_next]
  change residual (runtime.advance steps).tick.next
    (next (runtime.advance steps) (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps)
      (read (inventoryBound runtime + steps + 1))) key = _
  rw [receipt_at runtime read steps]
  exact residual_next (runtime.advance steps) _ read key (trajectory_native runtime initial read source steps)

theorem trajectory_energy (runtime : LivingRuntimeState process) (initial : At runtime Key) (read : Nat → Key) (key : Key)
    (source : initial.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) (steps : Nat) :
    ‖residual (runtime.advance (steps + 1))
      (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) (steps + 1)) key‖ ^ 2 =
      if key = read (inventoryBound runtime + steps + 1) then
        (SourceStableReceivedCount.contraction
          ((trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps).native key).1 : ℝ) ^ 2 *
          ‖residual (runtime.advance steps) (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps) key‖ ^ 2
      else ‖residual (runtime.advance steps) (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps) key‖ ^ 2 := by
  rw [trajectory_residual runtime initial read key source steps]
  split_ifs
  · rw [norm_smul, mul_pow, Complex.norm_ratCast, sq_abs]
  · rfl

theorem trajectory_error_step (runtime : LivingRuntimeState process) (initial : At runtime Key) (read : Nat → Key) (key : Key)
    (source : initial.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) (steps : Nat) :
    ‖residual (runtime.advance (steps + 1)) (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) (steps + 1)) key‖ ^ 2 ≤
      ‖residual (runtime.advance steps) (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps) key‖ ^ 2 := by
  rw [trajectory_energy runtime initial read key source steps]
  split_ifs
  · exact mul_le_of_le_one_left (sq_nonneg _) (contraction_square _)
  · rfl

theorem trajectory_error_bound (runtime : LivingRuntimeState process) (initial : At runtime Key) (read : Nat → Key) (key : Key)
    (source : initial.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) (steps : Nat) :
    ‖residual (runtime.advance steps) (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps) key‖ ^ 2 ≤
      ‖residual runtime initial key‖ ^ 2 := by
  induction steps with
  | zero =>
    simpa only [trajectory_zero, LivingRuntimeState.advance] using (le_refl (‖residual runtime initial key‖ ^ 2))
  | succ steps previous =>
    exact (trajectory_error_step runtime initial read key source steps).trans previous

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
