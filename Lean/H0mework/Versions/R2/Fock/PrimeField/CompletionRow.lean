import H0mework.Versions.R2.Fock.PrimeField.CompletionLift
import H0mework.Realization.Operations.SuccessorBoundary

/-! Original prime observations are exact reads of the existing successor primitive and its retained unit mass. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCompletion

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery

noncomputable section

def cut (prime : Nat.Primes) : Nat := (prime.val - 3) / 2

theorem prime_threshold (prime : Nat.Primes) (state : Nat) :
    prime.val ≤ 2 * (state + 2) ↔ cut prime ≤ state := by
  unfold cut
  omega

def sourceRow (prime : Nat.Primes) (stage : Nat) : SourceOperationNative.Carrier process →ₗ[ℤ] ℤ :=
  if cut prime ≤ stage then SourceSuccessorBoundary.mass ℤ
  else (Finsupp.lapply (R := ℤ) (M := ℤ) (cut prime - stage - 1)).comp (SourceSuccessorBoundary.certificate ℤ)

theorem sourceRow_point (prime : Nat.Primes) (stage state : Nat) :
    sourceRow prime stage (SourceOperationNative.statePoint process state) =
      if cut prime ≤ state + stage then 1 else 0 := by
  unfold sourceRow
  by_cases early : cut prime ≤ stage
  · rw [if_pos early, if_pos (by omega)]
    exact SourceSuccessorBoundary.mass_single ℤ state 1
  · rw [if_neg early]
    change (SourceSuccessorBoundary.certificate ℤ (Finsupp.single state 1)) (cut prime - stage - 1) = _
    rw [SourceSuccessorBoundary.certificate_single]
    simp only [one_smul, Finset.sum_apply', Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_range]
    have same : cut prime - stage - 1 < state ↔ cut prime ≤ state + stage := by omega
    simp only [same]

theorem source_row_is_prime_read (prime : Nat.Primes) (stage : Nat) :
    sourceRow prime stage = (primeRead prime).comp (stageEvaluator nativeAction observation stage) := by
  apply Finsupp.lhom_ext'
  intro state
  apply LinearMap.ext_ring
  change sourceRow prime stage (SourceOperationNative.statePoint process state) =
    primeRead prime (observation ((nativeAction ^ stage) (SourceOperationNative.statePoint process state)))
  rw [sourceRow_point, source_iterate, SourceOperationNative.observer_statePoint, primeRead_source]
  simp only [prime_threshold]

end
end SourcePrimeCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
