import H0mework.Fock.PrimeField.RecoveryModel
import H0mework.Probability.EmpiricalRecovery.FiniteTransfer

/-! One source-generated prime supplies a finite query for every actor in the original bounded history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeHistoryRecovery

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open SourceGeneratedActionObservationHistory SourceGeneratedRuntimeHistoryProbability

noncomputable section

def windowBound (owner : GlobalParentOwner) (bound : Nat) : Nat := delay owner (bound + 1) + bound + 1
abbrev Raw (owner : GlobalParentOwner) (bound : Nat) := Fin (windowBound owner bound + 1) → IntegralOneParticle

def offset (owner : GlobalParentOwner) (bound : Nat) (index : Fin (bound + 1)) : Fin (windowBound owner bound) :=
  ⟨delay owner (bound + 1) + (bound - index.val), by unfold windowBound; omega⟩

def coefficient (owner : GlobalParentOwner) (bound : Nat) (index : Fin (bound + 1)) : Raw owner bound →ₗ[ℤ] ℤ :=
  (primeRead (selectedPrime owner (bound + 1))).comp
    ((LinearMap.proj (offset owner bound index).succ : Raw owner bound →ₗ[ℤ] IntegralOneParticle) -
      (LinearMap.proj (offset owner bound index).castSucc))

abbrev observe (owner : GlobalParentOwner) (bound : Nat) :=
  FiniteRecurrence.Native.query (process := process) rawField (windowBound owner bound) runtimeSeed bound

theorem query_value (owner : GlobalParentOwner) (bound : Nat) (index : Fin (bound + 1))
    (time : Fin (windowBound owner bound + 1)) :
    observe owner bound index time = rawField (index.val + 1 + time.val) := by
  change FiniteRecurrence.Native.rawWindow rawField (windowBound owner bound)
    ((history runtimeSeed bound).stageAt index).next time = _
  rw [FiniteRecurrence.Native.rawWindow_source]
  have point : SourceOperationNative.point ((history runtimeSeed bound).stageAt index).next =
      SourceOperationNative.statePoint process (index.val + 1) :=
    congrArg (SourceOperationNative.statePoint process) (runtimeAt_state (index.val + 1))
  rw [point]
  change observation ((nativeAction ^ time.val) (SourceOperationNative.statePoint process (index.val + 1))) = _
  rw [source_iterate, SourceOperationNative.observer_statePoint]

theorem coefficient_query (owner : GlobalParentOwner) (bound : Nat) (index actor : Fin (bound + 1)) :
    coefficient owner bound index (observe owner bound actor) = if actor = index then 1 else 0 := by
  change primeRead (selectedPrime owner (bound + 1))
    (observe owner bound actor (offset owner bound index).succ -
      observe owner bound actor (offset owner bound index).castSucc) = _
  rw [map_sub, query_value, query_value]
  have first : actor.val + 1 + (offset owner bound index).succ.val =
      (actor.val + 1 + (bound - index.val)) + delay owner (bound + 1) + 1 := by
    simp only [offset, Fin.val_succ]
    omega
  have second : actor.val + 1 + (offset owner bound index).castSucc.val =
      (actor.val + 1 + (bound - index.val)) + delay owner (bound + 1) := by
    simp only [offset, Fin.val_castSucc]
    omega
  rw [first, second, point_separation]
  have same : actor.val + 1 + (bound - index.val) = bound + 1 ↔ actor = index := by
    rw [Fin.ext_iff]
    omega
  simp only [same]

theorem observe_injective (owner : GlobalParentOwner) (bound : Nat) :
    Function.Injective (observe owner bound) := by
  intro left right same
  have selected := congrArg (coefficient owner bound left) same
  rw [coefficient_query, coefficient_query, if_pos rfl] at selected
  by_contra different
  rw [if_neg (Ne.symm different)] at selected
  exact one_ne_zero selected

end
end SourcePrimeHistoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
