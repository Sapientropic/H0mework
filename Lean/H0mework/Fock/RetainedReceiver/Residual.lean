import H0mework.Fock.RetainedReceiver.Model

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*} [DecidableEq Key]
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem residual_next (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key) (key : Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) :
    residual runtime.tick.next (next runtime frame (read runtime.tick.next.state)) key =
      if key = read runtime.tick.next.state then
        (SourceStableReceivedCount.contraction (frame.native key).1 : ℂ) • residual runtime frame key
      else residual runtime frame key := by
  have receipt := congrArg read ((inventory_bound runtime.tick.next).symm.trans (SourceActualImageStep.next_bound runtime))
  have count := congrArg (fun state : SourceConditionalNativeObservers.State Key (inventoryBound runtime) => (state key).1) source
  simp only [residual, next_value,
    model_source runtime.tick.next _ read key (next_native runtime frame read source), model_source runtime frame read key source]
  change (if key = read runtime.tick.next.state then value runtime frame key +
    ((((frame.native key).1 + 1 : Nat) : ℚ)⁻¹ : ℂ) • (SourceConditionalInventory.born (inventoryBound runtime) - value runtime frame key)
    else value runtime frame key) - SourceConditionalNativePosterior.decoder runtime.tick.next read key =
      if key = read runtime.tick.next.state then
        (SourceStableReceivedCount.contraction (frame.native key).1 : ℂ) •
          (value runtime frame key - SourceConditionalNativePosterior.decoder runtime read key)
      else value runtime frame key - SourceConditionalNativePosterior.decoder runtime read key
  rw [SourceConditionalNativeBirth.decoder_next, receipt, count]
  have factor := congrArg (fun scalar : ℚ => (scalar : ℂ))
    (SourceStableReceivedCount.contraction_formula (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).1)
  simp only [Rat.cast_sub, Rat.cast_one] at factor
  rw [← factor]
  split_ifs <;> module

theorem residual_energy (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key) (key : Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) :
    ‖residual runtime.tick.next (next runtime frame (read runtime.tick.next.state)) key‖ ^ 2 =
      if key = read runtime.tick.next.state then
        (SourceStableReceivedCount.contraction (frame.native key).1 : ℝ) ^ 2 * ‖residual runtime frame key‖ ^ 2
      else ‖residual runtime frame key‖ ^ 2 := by
  rw [residual_next runtime frame read key source]
  split_ifs
  · rw [norm_smul, mul_pow, Complex.norm_ratCast, sq_abs]
  · rfl

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
