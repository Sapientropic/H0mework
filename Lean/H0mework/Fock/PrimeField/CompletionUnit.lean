import H0mework.Fock.PrimeField.CompletionConservation

/-! A finite source witness and its retained primitive support rule out a hidden unit at infinity. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCompletion

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery

noncomputable section

theorem primitive_constant_of_coefficients_zero (owner : GlobalParentOwner) (value : Field)
    (invisible : ∀ index, coefficient owner index value = 0) (index : Nat) :
    primitive owner index value = mass value := by
  induction index with
  | zero =>
      have unit := coefficient_zero owner value
      rw [invisible 0] at unit
      omega
  | succ index previous =>
      have source := coefficient_successor owner value index
      rw [invisible (index + 1), previous] at source
      omega

theorem prime_read_is_mass_of_coefficients_zero (owner : GlobalParentOwner) (value : Field)
    (invisible : ∀ index, coefficient owner index value = 0) (prime : Nat.Primes) (stage : Nat) :
    primeRead prime (read stage value) = mass value := by
  rw [source_row_on_completion owner]
  simp only [primitive_constant_of_coefficients_zero owner value invisible, ite_self]

theorem mass_zero_of_coefficients_zero (owner : GlobalParentOwner) (value : Field)
    (invisible : ∀ index, coefficient owner index value = 0) : mass value = 0 := by
  obtain ⟨word, agrees⟩ := finite_source_reads value 0
  let oldPrimitive := SourceSuccessorBoundary.certificate ℤ word
  let bound := oldPrimitive.support.sup id
  let prime : Nat.Primes := selectedPrime owner bound
  have position := selected_cut owner bound
  have delayed := delay_positive owner bound
  have high : bound < cut prime - 1 := by
    change bound < cut (selectedPrime owner bound) - 1
    omega
  have outside : cut prime - 1 ∉ oldPrimitive.support := by
    intro member
    have smaller : cut prime - 1 ≤ bound := Finset.le_sup (f := id) member
    omega
  have tailZero := Finsupp.notMem_support_iff.mp outside
  have sourceZero : sourceRow prime 0 word = 0 := by
    unfold sourceRow
    rw [if_neg (by omega)]
    change oldPrimitive (cut prime - 0 - 1) = 0
    simpa only [Nat.sub_zero] using tailZero
  calc
    mass value = primeRead prime (read 0 value) :=
      (prime_read_is_mass_of_coefficients_zero owner value invisible prime 0).symm
    _ = primeRead prime (read 0 (sourceMap nativeAction observation word)) :=
      congrArg (primeRead prime) (agrees 0 le_rfl).symm
    _ = primeRead prime (observation ((nativeAction ^ 0) word)) := congrArg (primeRead prime) (read_source 0 word)
    _ = sourceRow prime 0 word := (LinearMap.congr_fun (source_row_is_prime_read prime 0) word).symm
    _ = 0 := sourceZero

end
end SourcePrimeCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
