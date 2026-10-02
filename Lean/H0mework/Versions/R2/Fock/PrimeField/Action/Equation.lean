import H0mework.Versions.R2.Fock.PrimeField.CompletionRow
import H0mework.Realization.Operations.Primitive

/-! The original prime row reads the actual source successor and its complete
finite-word increment before any coimage action is constructed. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeActionEquation

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery SourcePrimeCompletion
open SourceGeneratedScalarDifferentialResidual

noncomputable section

theorem source_action_equation (prime : Nat.Primes) (stage : Nat)
    (word : SourceOperationNative.Carrier process) :
    sourceRow prime stage (nativeAction word) = sourceRow prime stage word +
      if cut prime ≤ stage then 0 else word (cut prime - stage - 1) := by
  change sourceRow prime stage (SourceSuccessorBoundary.push ℤ word) = _
  by_cases inside : cut prime ≤ stage
  · simp only [sourceRow, if_pos inside, add_zero]
    exact SourceSuccessorBoundary.mass_push ℤ word
  · simp only [sourceRow, if_neg inside, LinearMap.comp_apply, Finsupp.lapply_apply]
    rw [SourceSuccessorBoundary.certificate_push]
    rfl

theorem source_action_stable (prime : Nat.Primes) (stage : Nat)
    (inside : cut prime ≤ stage) (word : SourceOperationNative.Carrier process) :
    sourceRow prime stage (nativeAction word) = sourceRow prime stage word := by
  simpa only [if_pos inside, add_zero] using source_action_equation prime stage word

def coimageAction (prime : Nat.Primes) (stage : Nat) (inside : cut prime ≤ stage) :
    ResidualCarrier (sourceRow prime stage) →ₗ[ℤ] ResidualCarrier (sourceRow prime stage) :=
  (LinearMap.ker (sourceRow prime stage)).liftQ
    ((canonicalResidual (sourceRow prime stage)).comp nativeAction) (by
      intro word invisible
      apply (canonicalResidual_eq_zero_iff (sourceRow prime stage) (nativeAction word)).mpr
      exact (source_action_stable prime stage inside word).trans invisible)

theorem coimage_action_source (prime : Nat.Primes) (stage : Nat)
    (inside : cut prime ≤ stage) (word : SourceOperationNative.Carrier process) :
    coimageAction prime stage inside (canonicalResidual (sourceRow prime stage) word) =
      canonicalResidual (sourceRow prime stage) (nativeAction word) := rfl

def invisibleWord (prime : Nat.Primes) (stage : Nat) : SourceOperationNative.Carrier process :=
  SourceOperationNative.statePoint process (cut prime - stage - 1)

theorem invisible_word_current (prime : Nat.Primes) (stage : Nat)
    (outside : stage < cut prime) : sourceRow prime stage (invisibleWord prime stage) = 0 := by
  rw [invisibleWord, sourceRow_point, if_neg]
  omega

theorem invisible_word_next (prime : Nat.Primes) (stage : Nat)
    (outside : stage < cut prime) :
    sourceRow prime stage (nativeAction (invisibleWord prime stage)) = 1 := by
  rw [source_action_equation, invisible_word_current prime stage outside, if_neg (by omega)]
  simp only [invisibleWord, SourceOperationNative.statePoint, Finsupp.single_eq_same, zero_add]

end
end SourcePrimeActionEquation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
