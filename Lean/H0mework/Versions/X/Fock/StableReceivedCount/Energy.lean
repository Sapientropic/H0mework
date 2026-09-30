import H0mework.Versions.X.Fock.StableReceivedCount.Residual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceStableReceivedCount

theorem contraction_nonnegative (members : Nat) : 0 ≤ contraction members := by
  unfold contraction
  positivity

theorem contraction_lt_one (members : Nat) : contraction members < 1 := by
  unfold contraction
  apply (div_lt_one (by positivity : (0 : ℚ) < (members + 1 : Nat))).mpr
  exact_mod_cast Nat.lt_succ_self members

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem residual_energy (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Key) (key : Key)
    (budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    ‖nextValue runtime nonunit samples (decide (key = read runtime.tick.next.state)) -
      SourceConditionalNativePosterior.decoder runtime.tick.next read key‖ ^ 2 =
      let oldError := SourceReceivedConditionalStep.completeValue runtime (maximumIndex runtime) 0
        (SourceRationalWindowReadout.decode (inventoryBound runtime) (maximumIndex runtime).val samples) -
          SourceConditionalNativePosterior.decoder runtime read key
      if key = read runtime.tick.next.state then
        (contraction (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).1 : ℝ)^2 * ‖oldError‖^2
      else ‖oldError‖^2 := by
  rw [residual_from_precision runtime nonunit samples read key budget]
  dsimp only
  split_ifs
  · rw [norm_smul, mul_pow, Complex.norm_ratCast, sq_abs]
  · rfl

end
end SourceStableReceivedCount
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
