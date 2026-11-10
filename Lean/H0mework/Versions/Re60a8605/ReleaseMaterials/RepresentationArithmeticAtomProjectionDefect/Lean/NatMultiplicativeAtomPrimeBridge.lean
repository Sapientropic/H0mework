import Mathlib.Data.Nat.Prime.Basic
import H0mework.Arithmetic.ProjectionDefect.AtomProjectionDefectCore

/-!
# Natural multiplicative atom / prime compatibility

This file records that the local multiplicative atom predicate on natural
numbers matches Mathlib's `Nat.Prime`, without changing the main pipeline to
use naked prime predicates.
-/

namespace RepresentationArithmeticAtomProjectionDefect

/-- Units of the natural-number multiplicative monoid have value `1`. -/
private theorem nat_eq_one_of_isUnit {m : Nat} (h : IsUnit m) :
    m = 1 := by
  rcases h with ⟨u, hu⟩
  rw [← hu]
  exact (mul_eq_one.mp u.val_inv).1

/-- The local natural-number multiplicative atom predicate agrees with
Mathlib's natural-number prime predicate.

This is a compatibility theorem, not a change of ontology for the bridge:
endpoint objects remain `MultiplicativeAtomCode NatMultiplicativelyAtomic`.
-/
theorem natMultiplicativelyAtomic_iff_nat_prime (m : Nat) :
    NatMultiplicativelyAtomic m ↔ Nat.Prime m :=
  by
    constructor
    · intro hAtomic
      rcases hAtomic with ⟨hNeOne, hFactors⟩
      refine {
        not_isUnit := ?_
        isUnit_or_isUnit := ?_
      }
      · intro hUnit
        exact hNeOne (nat_eq_one_of_isUnit hUnit)
      · intro a b hMul
        rcases hFactors hMul with hLeft | hRight
        · left
          rw [hLeft]
          exact isUnit_one
        · right
          rw [hRight]
          exact isUnit_one
    · intro hPrime
      exact ⟨hPrime.ne_one, by
        intro a b hMul
        rcases hPrime.isUnit_or_isUnit hMul with hLeft | hRight
        · left
          exact nat_eq_one_of_isUnit hLeft
        · right
          exact nat_eq_one_of_isUnit hRight
      ⟩

/-- A multiplicatively atomic natural code is prime in Mathlib's sense. -/
theorem nat_prime_of_multiplicatively_atomic {m : Nat}
    (h : NatMultiplicativelyAtomic m) :
    Nat.Prime m :=
  (natMultiplicativelyAtomic_iff_nat_prime m).mp h

/-- A Mathlib prime natural number is a multiplicative atom in the local
endpoint-code sense. -/
theorem nat_multiplicatively_atomic_of_prime {m : Nat}
    (h : Nat.Prime m) :
    NatMultiplicativelyAtomic m :=
  (natMultiplicativelyAtomic_iff_nat_prime m).mpr h

/-- Build a local multiplicative atom code from a Mathlib prime certificate. -/
def natMultiplicativeAtomCodeOfPrime
    (m : Nat) (h : Nat.Prime m) :
    NatMultiplicativeAtomCode where
  code := m
  atomic := nat_multiplicatively_atomic_of_prime h


end RepresentationArithmeticAtomProjectionDefect
