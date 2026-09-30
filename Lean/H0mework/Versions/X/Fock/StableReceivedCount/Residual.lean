import H0mework.Versions.X.Fock.StableReceivedCount.Action

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceStableReceivedCount

def contraction (members : Nat) : ℚ := (members : ℚ) / ((members + 1 : Nat) : ℚ)

theorem contraction_formula (members : Nat) : 1 - (((members + 1 : Nat) : ℚ)⁻¹) = contraction members := by
  have nonzero : ((members + 1 : Nat) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero members)
  unfold contraction
  push_cast
  field_simp
  ring

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem residual_from_precision (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Key) (key : Key)
    (budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    nextValue runtime nonunit samples (decide (key = read runtime.tick.next.state)) -
      SourceConditionalNativePosterior.decoder runtime.tick.next read key =
      let oldError := SourceReceivedConditionalStep.completeValue runtime (maximumIndex runtime) 0
        (SourceRationalWindowReadout.decode (inventoryBound runtime) (maximumIndex runtime).val samples) -
          SourceConditionalNativePosterior.decoder runtime read key
      if key = read runtime.tick.next.state then
        (contraction (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).1 : ℂ) • oldError
      else oldError := by
  dsimp only
  have actual := count_complete runtime nonunit samples read key budget
  have receipt := congrArg read ((inventory_bound runtime.tick.next).symm.trans (SourceActualImageStep.next_bound runtime))
  rw [next_value_source, actual, SourceConditionalNativeBirth.decoder_next, receipt]
  simp only [decide_eq_true_eq]
  have factor := congrArg (fun scalar : ℚ => (scalar : ℂ))
    (contraction_formula (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).1)
  simp only [Rat.cast_sub, Rat.cast_one] at factor
  rw [← factor]
  split_ifs <;> module

end
end SourceStableReceivedCount
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
