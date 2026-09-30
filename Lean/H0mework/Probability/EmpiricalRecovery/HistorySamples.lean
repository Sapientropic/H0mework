import H0mework.Realization.HilbertTransfer.ChainRecovery
import H0mework.Probability.Empirical.History
import H0mework.Probability.Empirical.Decoder

/-! The old history inverse evaluates a terminal estimator on the same actual advanced source indices. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRecovery.History

open SourceGeneratedEmpiricalHilbert SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

def liftEstimator (depth : Nat) (decoder : Space read (runtime.advance depth) bound) : Space read runtime bound :=
  (retainedHistory read runtime bound depth).symm (decoder, 0)

theorem liftEstimator_at_sample (depth : Nat) (decoder : Space read (runtime.advance depth) bound)
    (index : Fin (bound + 1)) :
    liftEstimator read runtime bound depth decoder (fieldSample read runtime bound index) =
      decoder (fieldSample read (runtime.advance depth) bound index) := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
      have lifted := IsometricRetainedTransfer.Chain.source_lift_succ
        (H := fun stage => Space read (runtime.advance stage) bound)
        (stagePullback read runtime bound) depth decoder
      have sampled := congrArg (fun value : Space read runtime bound => value (fieldSample read runtime bound index)) lifted
      exact sampled.trans ((previous (pullback read (runtime.advance depth) bound decoder)).trans
        ((pullback_at_sample read (runtime.advance depth) bound decoder index).trans
          (congrArg decoder (nextAtom_eq_next_sample read (runtime.advance depth) bound index))))

def terminalError (depth : Nat) (value : Space read runtime bound) (decoder : Field read → ℂ) : ℝ :=
  ∑ index : Fin (bound + 1), (historyPMF bound index).toReal *
    ‖value (fieldSample read runtime bound index) - decoder (fieldSample read (runtime.advance (depth + 1)) bound index)‖ ^ 2

theorem terminalError_eq_norm (depth : Nat) (value : Space read runtime bound) (decoder : Field read → ℂ) :
    terminalError read runtime bound depth value decoder =
      ‖value - liftEstimator read runtime bound (depth + 1)
        (decoderValue read (runtime.advance depth) bound decoder)‖ ^ 2 := by
  rw [terminalError, sample_norm_sq]
  apply Finset.sum_congr rfl
  intro index _
  have evaluated := (sampleRead read runtime bound index).map_sub value
    (liftEstimator read runtime bound (depth + 1) (decoderValue read (runtime.advance depth) bound decoder))
  change (value - liftEstimator read runtime bound (depth + 1)
      (decoderValue read (runtime.advance depth) bound decoder)) (fieldSample read runtime bound index) =
    value (fieldSample read runtime bound index) - liftEstimator read runtime bound (depth + 1)
      (decoderValue read (runtime.advance depth) bound decoder) (fieldSample read runtime bound index) at evaluated
  rw [evaluated]
  have atomEq := nextAtom_eq_next_sample read (runtime.advance depth) bound index
  have lifted := liftEstimator_at_sample read runtime bound (depth + 1)
    (decoderValue read (runtime.advance depth) bound decoder) index
  have readback := (congrArg (decoderValue read (runtime.advance depth) bound decoder) atomEq.symm).trans
    ((decoderValue_at_next read (runtime.advance depth) bound decoder index).trans (congrArg decoder atomEq))
  exact congrArg (fun estimate : ℂ => (historyPMF bound index).toReal *
    ‖value (fieldSample read runtime bound index) - estimate‖ ^ 2) (lifted.trans readback).symm

end
end SourceConditionalRecovery.History
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
