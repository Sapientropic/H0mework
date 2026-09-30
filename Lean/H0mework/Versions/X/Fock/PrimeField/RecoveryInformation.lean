import H0mework.Versions.X.Fock.PrimeField.RecoveryWindow
import H0mework.Probability.Recovery.Fibre
import H0mework.Versions.X.Fock.SourceHistory.ConditionalActorInstalled

/-! Source-paid prime queries recover the old complete conditional and actor-to-field transfer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeHistoryRecovery

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourceGeneratedRuntimeHistoryProbability
open SourceConditionalTransfer SourceWeightedRecovery
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

local instance : UniformSpace (Field (process := process) rawField) := fieldUniform (process := process) rawField
local instance : MeasurableSpace (Field (process := process) rawField) := fieldBorel (process := process) rawField
local instance : BorelSpace (Field (process := process) rawField) := ⟨rfl⟩
local instance : T2Space (Field (process := process) rawField) := field_t2 (process := process) rawField

def decoder (owner : GlobalParentOwner) (bound : Nat) (task : Fin (bound + 1) → ℂ)
    (samples : Raw owner bound) : ℂ :=
  ∑ index : Fin (bound + 1), (coefficient owner bound index samples : ℂ) * task index

theorem decoder_query (owner : GlobalParentOwner) (bound : Nat) (task : Fin (bound + 1) → ℂ)
    (index : Fin (bound + 1)) : decoder owner bound task (observe owner bound index) = task index := by
  classical
  simp [decoder, coefficient_query]

theorem nextAtom_injective (owner : GlobalParentOwner) (bound : Nat) :
    Function.Injective (nextAtom (process := process) rawField runtimeSeed bound) := by
  intro left right same
  apply observe_injective owner bound
  have read := congrArg (FiniteRecurrence.Native.fieldRead (process := process) rawField (windowBound owner bound)) same
  simpa only [FiniteRecurrence.Native.fieldRead_query] using read

theorem conditional_pure (owner : GlobalParentOwner) (bound : Nat) (index : Fin (bound + 1)) :
    FiniteRecurrence.Native.conditional (process := process) rawField (windowBound owner bound) runtimeSeed bound index = PMF.pure index :=
  ObservationRefinement.conditional_injective (historyPMF bound) (observe owner bound)
    (observe_injective owner bound) index (by simp [historyPMF])

theorem conditional_is_original (owner : GlobalParentOwner) (bound : Nat) (index : Fin (bound + 1)) :
    FiniteRecurrence.Native.conditional (process := process) rawField (windowBound owner bound) runtimeSeed bound index =
      conditionalIndices (process := process) rawField runtimeSeed bound (nextAtom (process := process) rawField runtimeSeed bound index)
        (SourceConditionalRecovery.nextAtom_supported (process := process) rawField runtimeSeed bound index) := by
  have original := ObservationRefinement.conditional_injective (historyPMF bound)
    (nextAtom (process := process) rawField runtimeSeed bound) (nextAtom_injective owner bound) index (by simp [historyPMF])
  exact (conditional_pure owner bound index).trans original.symm

theorem complete_recovers (owner : GlobalParentOwner) (bound : Nat) (task : Fin (bound + 1) → ℂ)
    (index : Fin (bound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField runtimeSeed bound
        (Runtime.Actor.actorTransfer (process := process) rawField runtimeSeed bound (taskValue (historyPMF bound) task))
        (nextAtom (process := process) rawField runtimeSeed bound index) = task index :=
  (Runtime.Actor.completeTransfer_is_conditional (process := process) rawField runtimeSeed bound task
    (nextAtom (process := process) rawField runtimeSeed bound index)).trans
    (ObservationRefinement.optimum_injective (historyPMF bound) (nextAtom (process := process) rawField runtimeSeed bound)
      (nextAtom_injective owner bound) task index (by simp [historyPMF]))

theorem complete_transfer (owner : GlobalParentOwner) (bound : Nat) (task : Fin (bound + 1) → ℂ)
    (index : Fin (bound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField runtimeSeed bound
        (Runtime.Actor.actorTransfer (process := process) rawField runtimeSeed bound (taskValue (historyPMF bound) task))
        (nextAtom (process := process) rawField runtimeSeed bound index) =
      ∑ candidate : Fin (bound + 1),
        (FiniteRecurrence.Native.conditional (process := process) rawField (windowBound owner bound) runtimeSeed bound index candidate).toReal • task candidate := by
  rw [complete_recovers owner, conditional_pure]
  rw [Finset.sum_eq_single index]
  · simp [PMF.pure_apply]
  · intro candidate _ different
    simp [PMF.pure_apply, different]
  · simp

theorem raw_error_zero (owner : GlobalParentOwner) (bound : Nat) (task : Fin (bound + 1) → ℂ) :
    Runtime.Actor.rawError (process := process) rawField runtimeSeed bound task
      (fun atom => decoder owner bound task (FiniteRecurrence.Native.fieldRead (process := process) rawField (windowBound owner bound) atom)) = 0 := by
  rw [← FiniteRecurrence.Native.finiteError_is_original (process := process)]
  simp only [error, decoder_query, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]

end
end SourcePrimeHistoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
