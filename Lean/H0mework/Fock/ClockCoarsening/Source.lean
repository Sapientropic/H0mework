import H0mework.Probability.Source.ConditionalCoarsening
import H0mework.Fock.FiniteObservers.PulseConsumer
import H0mework.Probability.Runtime.Conditional
import H0mework.Realization.Operations.RuntimeSuccessor
import H0mework.Probability.Runtime.AffineClock
import H0mework.Probability.Recovery.Fibre

/-! The fixed canonical source generates the collapse of its original pulse observation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePulseCoarsening

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedEmpiricalHilbert.Controls
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical

noncomputable section

abbrev observe (bound : Nat) := SourceConditionalHistory.Runtime.observation runtimeSeed bound pulse
abbrev nextObserve (bound : Nat) := SourceConditionalHistory.Runtime.observation runtimeSeed.tick.next bound pulse

def forget : ZMod 2 → ZMod 2 := fun _ => 0

theorem source_pulse_next (state : process.State) : pulse (process.successor state) = 0 := by
  have generated := LinearMap.congr_fun SourceFiniteObservation.pulse_source_law
    (SourceOperationNative.statePoint process state)
  rw [LinearMap.comp_apply,
    show SourceOperationNative.sourceAction process ^ (0 + 1) = SourceOperationNative.sourceAction process from pow_one _] at generated
  simpa only [SourceOperationNative.sourceAction_statePoint,
    SourceOperationNative.observer_statePoint, zero_smul, Finset.sum_const_zero, LinearMap.zero_apply] using generated

theorem observe_actual (bound : Nat) (point : Fin (bound + 1)) :
    observe bound point = if point.val = 0 then (1 : ZMod 2) else 0 := by
  change pulse (runtimeAt point.val).state = _
  rw [runtimeAt_state]
  rfl

theorem next_observe_source (bound : Nat) (point : Fin (bound + 1)) :
    nextObserve bound point = forget (observe bound point) := by
  change pulse (runtimeSeed.tick.next.advance point.val).state = 0
  rw [SourceOperationRuntime.runtime_tail]
  change pulse (runtimeAt (point.val + 1)).state = 0
  rw [runtimeAt_state]
  exact source_pulse_next point.val

theorem forget_not_injective : ¬ Function.Injective forget := by
  intro injective
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0) (injective (a₁ := 1) (a₂ := 0) rfl)

def clockTask (bound : Nat) (point : Fin (bound + 1)) : ℂ :=
  ((sample runtimeSeed bound point : Nat) : ℂ)

theorem clock_actual (bound : Nat) (point : Fin (bound + 1)) :
    clockTask bound point = (point.val : ℂ) := by
  change ((runtimeAt point.val).state : ℂ) = _
  rw [runtimeAt_state]

theorem next_supported (bound : Nat) :
    (0 : ZMod 2) ∈ (SourceConditionalHistory.observed (historyPMF bound) (nextObserve bound)).support := by
  have actual := SourceConditionalHistory.Runtime.query_supported runtimeSeed.tick.next bound pulse
    (⟨0, Nat.succ_pos bound⟩ : Fin (bound + 1))
  simpa only [next_observe_source, forget] using actual

theorem next_conditional_full (bound : Nat) :
    SourceConditionalHistory.conditional (historyPMF bound) (nextObserve bound) 0 (next_supported bound) =
      historyPMF bound :=
  SourceWeightedRecovery.ObservationRefinement.conditional_constant _ _ 0
    (fun point => next_observe_source bound point) (next_supported bound)

end
end SourcePulseCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
