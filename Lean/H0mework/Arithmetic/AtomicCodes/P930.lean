import H0mework.Arithmetic.ShellSources.P929

/-!
# Proposition 930: Boolean atomic checks are exact and zero shells are pairs

P925 proved the sound direction of the executable endpoint checker:

```text
natMultiplicativelyAtomicCheck n = true -> NatMultiplicativelyAtomic n.
```

This file proves the converse and then ties P929's raw code-pair zero shell to
the ordinary bounded prime-pair statement.  The executable check still does not
store `Nat.Prime`; Lean proves that its truth value is exactly primality.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Boolean multiplicative-atomicity is exact -/

/-- Multiplicative atomicity rules out every Boolean nontrivial-divisor hit. -/
theorem natHasNontrivialDivisorCheck_eq_false_of_atomic
    {n : ℕ}
    (h : NatMultiplicativelyAtomic n) :
    natHasNontrivialDivisorCheck n = false := by
  unfold natHasNontrivialDivisorCheck
  apply List.any_eq_false.mpr
  intro a _ha htrue
  have hbad : 2 ≤ a ∧ a < n ∧ a ∣ n :=
    decide_eq_true_eq.mp htrue
  rcases hbad with ⟨ha2, halt, hdiv⟩
  rcases hdiv with ⟨b, hb⟩
  rcases h.2 a b hb with ha1 | hb1
  · omega
  · subst b
    omega

/-- Multiplicative atomicity makes the Boolean checker return `true`. -/
theorem natMultiplicativelyAtomicCheck_eq_true_of_atomic
    {n : ℕ}
    (h : NatMultiplicativelyAtomic n) :
    natMultiplicativelyAtomicCheck n = true := by
  unfold natMultiplicativelyAtomicCheck
  have h2 : decide (2 ≤ n) = true :=
    decide_eq_true_eq.mpr h.1
  have hnodiv :
      natHasNontrivialDivisorCheck n = false :=
    natHasNontrivialDivisorCheck_eq_false_of_atomic h
  simp [h2, hnodiv]

/-- The Boolean checker is equivalent to multiplicative atomicity. -/
theorem natMultiplicativelyAtomicCheck_eq_true_iff_atomic
    {n : ℕ} :
    natMultiplicativelyAtomicCheck n = true ↔
      NatMultiplicativelyAtomic n := by
  constructor
  · exact natMultiplicativelyAtomic_of_check_eq_true
  · exact natMultiplicativelyAtomicCheck_eq_true_of_atomic

/-- The Boolean checker is equivalent to primality, but the checker itself
does not mention `Nat.Prime`. -/
theorem natMultiplicativelyAtomicCheck_eq_true_iff_prime
    {n : ℕ} :
    natMultiplicativelyAtomicCheck n = true ↔ Nat.Prime n := by
  calc
    natMultiplicativelyAtomicCheck n = true
        ↔ NatMultiplicativelyAtomic n :=
      natMultiplicativelyAtomicCheck_eq_true_iff_atomic
    _ ↔ Nat.Prime n :=
      natMultiplicativelyAtomic_iff_prime

/-! ## Zero code-pair shells are exactly bounded Goldbach pairs -/

/-- A bounded prime pair in the even fiber `2n`. -/
def BoundedGoldbachPair (n bound : ℕ) : Prop :=
  ∃ p q : ℕ,
    p ∈ rawCodeBoundedList bound ∧
      q ∈ rawCodeBoundedList bound ∧
        Nat.Prime p ∧ Nat.Prime q ∧
          p + q = 2 * n

/-- A zero raw code-pair shell produces an ordinary bounded prime pair. -/
theorem boundedGoldbachPair_of_rawCodePairZeroShell
    {n bound : ℕ}
    (h : RawCodePairEnergyShellRealized n bound 0) :
    BoundedGoldbachPair n bound := by
  rcases h with
    ⟨left, right, hleft_mem, hright_mem,
      hleft_check, hright_check, henergy⟩
  refine ⟨left, right, hleft_mem, hright_mem, ?_, ?_, ?_⟩
  · exact
      (natMultiplicativelyAtomicCheck_eq_true_iff_prime).mp
        hleft_check
  · exact
      (natMultiplicativelyAtomicCheck_eq_true_iff_prime).mp
        hright_check
  ·
    have hres :
        rawCodePairResidual n left right = 0 := by
      exact Int.natAbs_eq_zero.mp henergy
    unfold rawCodePairResidual at hres
    omega

/-- A bounded prime pair produces a zero raw code-pair shell. -/
theorem rawCodePairZeroShell_of_boundedGoldbachPair
    {n bound : ℕ}
    (h : BoundedGoldbachPair n bound) :
    RawCodePairEnergyShellRealized n bound 0 := by
  rcases h with
    ⟨p, q, hp_mem, hq_mem, hp, hq, hsum⟩
  refine ⟨p, q, hp_mem, hq_mem, ?_, ?_, ?_⟩
  · exact
      (natMultiplicativelyAtomicCheck_eq_true_iff_prime).mpr hp
  · exact
      (natMultiplicativelyAtomicCheck_eq_true_iff_prime).mpr hq
  ·
    have hres : rawCodePairResidual n p q = 0 := by
      unfold rawCodePairResidual
      omega
    unfold rawCodePairResidualEnergy
    rw [hres]
    rfl

/-- P929's zero shell is exactly the bounded Goldbach-pair predicate. -/
theorem rawCodePairZeroShell_iff_boundedGoldbachPair
    (n bound : ℕ) :
    RawCodePairEnergyShellRealized n bound 0 ↔
      BoundedGoldbachPair n bound := by
  constructor
  · exact boundedGoldbachPair_of_rawCodePairZeroShell
  · exact rawCodePairZeroShell_of_boundedGoldbachPair

/-! ## Certificate -/

/-- P930 certificate: the Boolean endpoint checker is exact, and the zero
code-pair shell is exactly bounded Goldbach-pair existence. -/
structure SU7BooleanAtomicCheckExactnessCertificate where
  check_iff_atomic :
    ∀ n : ℕ,
      natMultiplicativelyAtomicCheck n = true ↔
        NatMultiplicativelyAtomic n
  check_iff_prime :
    ∀ n : ℕ,
      natMultiplicativelyAtomicCheck n = true ↔ Nat.Prime n
  zero_shell_iff_bounded_pair :
    ∀ n bound : ℕ,
      RawCodePairEnergyShellRealized n bound 0 ↔
        BoundedGoldbachPair n bound

/-- Canonical P930 exactness certificate. -/
def su7BooleanAtomicCheckExactnessCertificate :
    SU7BooleanAtomicCheckExactnessCertificate where
  check_iff_atomic := by
    intro n
    exact natMultiplicativelyAtomicCheck_eq_true_iff_atomic
  check_iff_prime := by
    intro n
    exact natMultiplicativelyAtomicCheck_eq_true_iff_prime
  zero_shell_iff_bounded_pair :=
    rawCodePairZeroShell_iff_boundedGoldbachPair


end
end StandardModelConstraint
end SaturationMonoid
