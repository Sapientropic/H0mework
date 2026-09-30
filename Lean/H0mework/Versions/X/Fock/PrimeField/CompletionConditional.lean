import H0mework.Versions.X.Fock.PrimeField.CompletionAction
import H0mework.Versions.X.Fock.PrimeFieldCalculation.CalculationConsumer

/-! The original conditional transfer reads the completed coefficient action at its own actual next atoms. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCompletion

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery SourceConditionalTransfer
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

theorem coefficient_next_atom (bound : Nat) (actor candidate : Fin (bound + 1)) :
    coefficient sourceOwner (candidate.val + 1) (nextAtom (process := process) rawField runtimeSeed bound actor) =
      if actor = candidate then 1 else 0 := by
  change coefficient sourceOwner (candidate.val + 1)
    (fieldAction (process := process) rawField (fieldSample (process := process) rawField runtimeSeed bound actor)) = _
  rw [coefficient_successor_advance]
  calc
    _ = (SourceOperationNative.statePoint process (sample runtimeSeed bound actor)) candidate.val :=
      coefficient_source sourceOwner candidate.val (SourceOperationNative.statePoint process (sample runtimeSeed bound actor))
    _ = _ := by
      change (Finsupp.single (runtimeAt actor.val).state (1 : ℤ)) candidate.val = _
      rw [runtimeAt_state, Finsupp.single_apply]
      simp only [Fin.ext_iff]

theorem conditional_weight_is_complete_coefficient (bound : Nat) (actor candidate : Fin (bound + 1)) :
    ((FiniteRecurrence.Native.conditional (process := process) rawField (windowBound sourceOwner bound) runtimeSeed bound actor candidate).toReal : ℂ) =
      (coefficient sourceOwner (candidate.val + 1) (nextAtom (process := process) rawField runtimeSeed bound actor) : ℂ) := by
  rw [SourcePrimeCalculation.conditional_weight_is_birth, SourcePrimeCalculation.birth_coefficient_is_delta, coefficient_next_atom]

theorem transfer_reads_complete_coefficients (bound : Nat) (task : Fin (bound + 1) → ℂ) (actor : Fin (bound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField runtimeSeed bound
      (Runtime.Actor.actorTransfer (process := process) rawField runtimeSeed bound (taskValue (historyPMF bound) task))
      (nextAtom (process := process) rawField runtimeSeed bound actor) =
      ∑ candidate : Fin (bound + 1),
        (coefficient sourceOwner (candidate.val + 1) (nextAtom (process := process) rawField runtimeSeed bound actor) : ℂ) * task candidate := by
  rw [complete_transfer sourceOwner]
  apply Finset.sum_congr rfl
  intro candidate _
  rw [Complex.real_smul, conditional_weight_is_complete_coefficient]

end
end SourcePrimeCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
