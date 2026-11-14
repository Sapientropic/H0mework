import H0mework.Versions.Rc19e94a5.Fock.PrimeField.CompletionRow
import H0mework.Realization.Operations.FiniteKernel

/-! The original prime observations generate their finite recurrence, then
consume the existing finite-prefix action and full-future kernel producer.
The carrier remains the entire native source lattice, with no finiteness
premise; every shorter window retains an actual source difference. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeActionSaturation

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery SourcePrimeCompletion
open SourceGeneratedActionObservationHistory

noncomputable section

abbrev originalRead (prime : Nat.Primes) := sourceRow prime 0

theorem original_iterate (prime : Nat.Primes) (stage : Nat) :
    (originalRead prime).comp (nativeAction ^ stage) = sourceRow prime stage := by
  apply Finsupp.lhom_ext'
  intro state
  apply LinearMap.ext_ring
  change sourceRow prime 0 ((nativeAction ^ stage) (SourceOperationNative.statePoint process state)) =
    sourceRow prime stage (SourceOperationNative.statePoint process state)
  rw [source_iterate, sourceRow_point, sourceRow_point]
  simp only [Nat.add_zero]

theorem original_saturated (prime : Nat.Primes) (stage : Nat) (inside : cut prime ≤ stage) :
    (originalRead prime).comp (nativeAction ^ stage) = SourceSuccessorBoundary.mass ℤ := by
  rw [original_iterate]
  simp only [sourceRow, if_pos inside]

def coefficients (prime : Nat.Primes) (index : Fin (cut prime + 1)) : ℤ :=
  if index = Fin.last (cut prime) then 1 else 0

theorem source_recurrence (prime : Nat.Primes) :
    (originalRead prime).comp (nativeAction ^ (cut prime + 1)) =
      ∑ index : Fin (cut prime + 1), coefficients prime index •
        stageEvaluator nativeAction (originalRead prime) index.val := by
  simp only [coefficients, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Fin.val_last, stageEvaluator]
  exact (original_saturated prime (cut prime + 1) (by omega)).trans
    (original_saturated prime (cut prime) (Nat.le_refl _)).symm

theorem finite_prefix_action (prime : Nat.Primes) :
    (FiniteRecurrence.advance (cut prime) (coefficients prime)).comp
      (prefixEvaluator nativeAction (originalRead prime) (cut prime)) =
    (prefixEvaluator nativeAction (originalRead prime) (cut prime)).comp nativeAction :=
  FiniteRecurrence.advance_source nativeAction (originalRead prime) (cut prime)
    (coefficients prime) (source_recurrence prime)

theorem finite_prefix_kernel_eq_full (prime : Nat.Primes) :
    LinearMap.ker (prefixEvaluator nativeAction (originalRead prime) (cut prime)) =
      LinearMap.ker (sourceMap nativeAction (originalRead prime)) :=
  FiniteRecurrence.prefix_kernel_eq_full nativeAction (originalRead prime) (cut prime)
    (coefficients prime) (source_recurrence prime)

theorem finite_prefix_fibre_iff_model (prime : Nat.Primes)
    (left right : SourceOperationNative.Carrier process) :
    prefixEvaluator nativeAction (originalRead prime) (cut prime) left =
      prefixEvaluator nativeAction (originalRead prime) (cut prime) right ↔
    projection nativeAction (originalRead prime) left =
      projection nativeAction (originalRead prime) right :=
  FiniteRecurrence.prefix_fibre_iff_model nativeAction (originalRead prime) (cut prime)
    (coefficients prime) (source_recurrence prime) left right

def shortWord (prime : Nat.Primes) (bound : Nat) : SourceOperationNative.Carrier process :=
  SourceOperationNative.statePoint process (cut prime - bound - 1)

theorem short_prefix_zero (prime : Nat.Primes) (bound : Nat) (outside : bound < cut prime) :
    prefixEvaluator nativeAction (originalRead prime) bound (shortWord prime bound) = 0 := by
  funext index
  change ((originalRead prime).comp (nativeAction ^ index.val)) (shortWord prime bound) = 0
  rw [original_iterate, shortWord, sourceRow_point, if_neg]
  omega

theorem short_next_one (prime : Nat.Primes) (bound : Nat) (outside : bound < cut prime) :
    originalRead prime ((nativeAction ^ (bound + 1)) (shortWord prime bound)) = 1 := by
  change ((originalRead prime).comp (nativeAction ^ (bound + 1))) (shortWord prime bound) = 1
  rw [original_iterate, shortWord, sourceRow_point, if_pos]
  omega

theorem short_prefix_next_nonzero (prime : Nat.Primes) (bound : Nat) (outside : bound < cut prime) :
    prefixEvaluator nativeAction (originalRead prime) bound (nativeAction (shortWord prime bound)) ≠ 0 := by
  intro vanishes
  have last := congrFun vanishes (Fin.last bound)
  change originalRead prime ((nativeAction ^ bound) (nativeAction (shortWord prime bound))) = 0 at last
  have next := short_next_one prime bound outside
  rw [pow_succ] at next
  exact one_ne_zero (next.symm.trans last)

theorem short_prefix_kernel_ne_full (prime : Nat.Primes) (bound : Nat) (outside : bound < cut prime) :
    LinearMap.ker (prefixEvaluator nativeAction (originalRead prime) bound) ≠
      LinearMap.ker (sourceMap nativeAction (originalRead prime)) := by
  intro same
  have invisible : shortWord prime bound ∈ LinearMap.ker (sourceMap nativeAction (originalRead prime)) := by
    rw [← same]
    exact short_prefix_zero prime bound outside
  have reading := (mem_kernel_iff nativeAction (originalRead prime) (shortWord prime bound)).mp
    invisible (bound + 1)
  exact one_ne_zero ((short_next_one prime bound outside).symm.trans reading)

end
end SourcePrimeActionSaturation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
