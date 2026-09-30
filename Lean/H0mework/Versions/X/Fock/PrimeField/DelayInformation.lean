import H0mework.Versions.X.Fock.PrimeField.DelayHistory
import H0mework.Probability.Runtime.AffineClock

/-! The unchanged finite observation retains the full actor posterior and its exact original clock cost. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeObservationDelay

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open SourcePrimeHistoryRecovery
open SourceGeneratedActionObservationHistory SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

def atom (owner : GlobalParentOwner) (bound width : Nat) : Fin (width + 1) → IntegralOneParticle :=
  fun _ => rawField (firstState owner (bound + width))

def clockTask (owner : GlobalParentOwner) (bound width : Nat) (actor : Fin (bound + 1)) : ℂ :=
  (sample (startRuntime owner bound width) bound actor : Nat)

theorem posterior_is_full (owner : GlobalParentOwner) (bound width : Nat) (index : Fin (bound + 1)) :
    FiniteRecurrence.Native.conditional (process := process) rawField width (startRuntime owner bound width) bound index =
      historyPMF bound :=
  ObservationRefinement.conditional_constant (historyPMF bound) (shortQuery owner bound width)
    (shortQuery owner bound width index)
    (fun actor => (query_constant owner bound width actor).trans (query_constant owner bound width index).symm)
    (FiniteRecurrence.Native.query_supported (process := process) rawField width (startRuntime owner bound width) bound index)

theorem clock_error (owner : GlobalParentOwner) (bound width : Nat) (decode : (Fin (width + 1) → IntegralOneParticle) → ℂ) :
    error (historyPMF bound) (shortQuery owner bound width) (clockTask owner bound width) decode =
      (bound : ℝ) * (bound + 2) / 12 +
        ‖(((firstState owner (bound + width) : ℝ) + bound / 2 : ℝ) : ℂ) - decode (atom owner bound width)‖ ^ 2 := by
  have query (actor : Fin (bound + 1)) : shortQuery owner bound width actor = atom owner bound width :=
    query_constant owner bound width actor
  simpa only [error, clockTask, sample_state, query, Nat.cast_add, mul_one,
    one_pow, one_mul, Complex.ofReal_add, Complex.ofReal_natCast] using
    ObservationRefinement.uniform_clock_error bound (firstState owner (bound + width)) 1 (decode (atom owner bound width))

theorem original_clock_error (owner : GlobalParentOwner) (bound width : Nat)
    (decode : (Fin (width + 1) → IntegralOneParticle) → ℂ) :
    Runtime.Actor.rawError (process := process) rawField (startRuntime owner bound width) bound (clockTask owner bound width)
      (fun field => decode (FiniteRecurrence.Native.fieldRead (process := process) rawField width field)) =
      (bound : ℝ) * (bound + 2) / 12 +
        ‖(((firstState owner (bound + width) : ℝ) + bound / 2 : ℝ) : ℂ) - decode (atom owner bound width)‖ ^ 2 :=
  (FiniteRecurrence.Native.finiteError_is_original (process := process) rawField width (startRuntime owner bound width) bound
    (clockTask owner bound width) decode).symm.trans (clock_error owner bound width decode)

theorem minimum_clock_cost (owner : GlobalParentOwner) (bound width : Nat) :
    error (historyPMF bound) (shortQuery owner bound width) (clockTask owner bound width)
      (fun _ => (((firstState owner (bound + width) : ℝ) + bound / 2 : ℝ) : ℂ)) =
      (bound : ℝ) * (bound + 2) / 12 := by
  rw [clock_error]
  simp

theorem clock_cost_positive (owner : GlobalParentOwner) (bound width : Nat) (hasMultiple : 0 < bound)
    (decode : (Fin (width + 1) → IntegralOneParticle) → ℂ) :
    0 < Runtime.Actor.rawError (process := process) rawField (startRuntime owner bound width) bound (clockTask owner bound width)
      (fun field => decode (FiniteRecurrence.Native.fieldRead (process := process) rawField width field)) := by
  rw [original_clock_error]
  have positive : (0 : ℝ) < bound := by exact_mod_cast hasMultiple
  positivity

end
end SourcePrimeObservationDelay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
