import H0mework.Fock.PrimeField.Action
import Mathlib.Data.Nat.Prime.Factorial

/-! Actual support growth identifies the possible new prime; the full multiplicity increment remains separate. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFactorizationAction.Fock

open ArithmeticGeneration
open CanonicalUnitArithmeticFactorizationOccurrence
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

noncomputable section

theorem whole_increment_apply (current : CanonicalUnitArithmeticRoot.Current) (prime : Nat.Primes) :
    wholeIncrement current prime = (2 * scanIndex current + 3).factorization prime.val +
      (2 * scanIndex current + 4).factorization prime.val := by
  change ((history current).cardinalShadow + 1).factorization prime.val +
    ((history current).cardinalShadow + 1 + 1).factorization prime.val = _
  rw [history_size]
  rfl

theorem primeCounts_support (history : UnitHistory) (prime : Nat.Primes) :
    prime ∈ (primeCounts history).support ↔ prime.val ≤ history.cardinalShadow := by
  rw [Finsupp.mem_support_iff]
  change factorization history prime.val ≠ 0 ↔ _
  rw [factorization_eq_cardinal_factorization]
  simp only [ne_eq, Nat.factorization_eq_zero_iff, prime.property, not_true_eq_false, false_or,
    Nat.factorial_ne_zero, or_false, not_not, prime.property.dvd_factorial]

def fresh (current : CanonicalUnitArithmeticRoot.Current) : Finset Nat.Primes :=
  (wholeIncrement current).support \ (primeCounts (history current)).support

theorem fresh_is_next_support (current : CanonicalUnitArithmeticRoot.Current) :
    fresh current = (primeCounts (history (CanonicalUnitArithmeticRoot.next current))).support \
      (primeCounts (history current)).support := by
  rw [counts_next, SourceSupportAction.support_add]
  ext prime
  simp only [fresh, Finset.mem_sdiff, Finset.mem_union]
  tauto

theorem fresh_iff (current : CanonicalUnitArithmeticRoot.Current) (prime : Nat.Primes) :
    prime ∈ fresh current ↔ prime.val = 2 * scanIndex current + 3 := by
  rw [fresh_is_next_support, Finset.mem_sdiff, primeCounts_support, primeCounts_support,
    history_size, history_size, scanIndex_next]
  have parity := prime.property.eq_two_or_odd
  rcases parity with two | odd <;> omega

theorem birth_of_prime (current : CanonicalUnitArithmeticRoot.Current)
    (isPrime : Nat.Prime (2 * scanIndex current + 3)) :
    birth current = atom ⟨2 * scanIndex current + 3, isPrime⟩ := by
  let candidate : Nat.Primes := ⟨2 * scanIndex current + 3, isPrime⟩
  have exactSupport : fresh current = {candidate} := by
    apply Finset.ext
    intro prime
    exact (fresh_iff current prime).trans
      ⟨fun same => Finset.mem_singleton.mpr (Subtype.ext same),
        fun member => congrArg Subtype.val (Finset.mem_singleton.mp member)⟩
  exact (congrArg (fun indices : Finset Nat.Primes => indices.sum atom) exactSupport).trans
    (Finset.sum_singleton atom candidate)

theorem birth_of_composite (current : CanonicalUnitArithmeticRoot.Current)
    (notPrime : ¬ Nat.Prime (2 * scanIndex current + 3)) : birth current = 0 := by
  have exactSupport : fresh current = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro prime member
    exact notPrime ((fresh_iff current prime).mp member ▸ prime.property)
  change (fresh current).sum atom = 0
  rw [exactSupport, Finset.sum_empty]

end
end SourceFactorizationAction.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
