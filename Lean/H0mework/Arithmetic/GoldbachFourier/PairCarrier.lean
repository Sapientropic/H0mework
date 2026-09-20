import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Goldbach prime-pair carrier

This file defines the arithmetic carrier shared by the exact, weighted, and
Fourier readouts of the Goldbach trace spine.  The pair is ordered, so it
matches the ordered convolution coefficient used by the circle method.

The exact prime fiber and the von Mangoldt correlation are deliberately
different objects.  Positivity of the full von Mangoldt correlation detects a
pair of prime powers.  Exact prime-pair existence is recovered only after the
prime-power correction is separated.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace GoldbachPrimePairTrace

/-! ## Generic additive pair geometry -/

/-- A pair geometry supplies the energy of one index.  Pair energy is derived
by addition; it is not stored as an independently assertable field. -/
structure AdditivePairGeometry (Index Energy : Type*) [Add Energy] where
  indexEnergy : Index → Energy

namespace AdditivePairGeometry

variable {Index Energy : Type*} [Add Energy]

/-- Ordered pair indices for a geometry. -/
abbrev Pair (_G : AdditivePairGeometry Index Energy) := Index × Index

/-- Additive energy of an ordered pair. -/
def pairEnergy (G : AdditivePairGeometry Index Energy) (pair : G.Pair) : Energy :=
  G.indexEnergy pair.1 + G.indexEnergy pair.2

/-- Fiber over one exact additive energy. -/
def Fiber (G : AdditivePairGeometry Index Energy) (target : Energy) :=
  { pair : G.Pair // G.pairEnergy pair = target }

end AdditivePairGeometry

/-! ## Exact prime-pair fiber -/

/-- Prime indices with their natural value as energy. -/
def primePairGeometry : AdditivePairGeometry Nat.Primes ℕ where
  indexEnergy p := p.1

/-- The exact ordered prime-pair fiber at `target`. -/
abbrev ExactPrimePairFiber (target : ℕ) :=
  AdditivePairGeometry.Fiber primePairGeometry target

/-- Pointwise Goldbach is nonemptiness of the exact prime-pair fiber. -/
def PointwiseGoldbachAt (target : ℕ) : Prop :=
  Nonempty (ExactPrimePairFiber target)

/-- Ordinary even Goldbach, stated directly on even targets at least four. -/
def EvenGoldbachStatement : Prop :=
  ∀ target : ℕ, Even target → 4 ≤ target → PointwiseGoldbachAt target

/-- The exact fiber is equivalent to the familiar two-prime equation. -/
theorem exactPrimePairFiber_nonempty_iff (target : ℕ) :
    Nonempty (ExactPrimePairFiber target) ↔
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = target := by
  constructor
  · rintro ⟨fiber⟩
    rcases fiber with ⟨⟨⟨p, hp⟩, ⟨q, hq⟩⟩, henergy⟩
    refine ⟨p, q, hp, hq, ?_⟩
    simpa [AdditivePairGeometry.pairEnergy, primePairGeometry] using henergy
  · rintro ⟨p, q, hp, hq, hsum⟩
    refine ⟨⟨(⟨p, hp⟩, ⟨q, hq⟩), ?_⟩⟩
    simpa [AdditivePairGeometry.pairEnergy, primePairGeometry] using hsum

/-! ## Finite natural correlations -/

/-- Ordered additive correlation on the finite window `1 ≤ a < target`. -/
def natPairCorrelation {R : Type*} [Semiring R]
    (weight : ℕ → R) (target : ℕ) : R :=
  ∑ a ∈ Finset.Ico 1 target, weight a * weight (target - a)

/-- Natural-valued prime indicator. -/
def primeIndicator (n : ℕ) : ℕ :=
  if Nat.Prime n then 1 else 0

@[simp] theorem primeIndicator_pos_iff (n : ℕ) :
    0 < primeIndicator n ↔ Nat.Prime n := by
  by_cases hn : Nat.Prime n <;> simp [primeIndicator, hn]

theorem primeIndicator_mul_pos_iff (p q : ℕ) :
    0 < primeIndicator p * primeIndicator q ↔
      Nat.Prime p ∧ Nat.Prime q := by
  by_cases hp : Nat.Prime p <;> by_cases hq : Nat.Prime q <;>
    simp [primeIndicator, hp, hq]

/-- Ordered exact prime-pair count. -/
def exactPrimePairCount (target : ℕ) : ℕ :=
  natPairCorrelation primeIndicator target

/-- Exact pair-count positivity is exactly nonemptiness of the prime fiber. -/
theorem exactPrimePairCount_pos_iff (target : ℕ) :
    0 < exactPrimePairCount target ↔
      Nonempty (ExactPrimePairFiber target) := by
  rw [exactPrimePairCount, natPairCorrelation, Finset.sum_pos_iff]
  constructor
  · rintro ⟨p, hpwindow, hppos⟩
    have hpq : Nat.Prime p ∧ Nat.Prime (target - p) :=
      (primeIndicator_mul_pos_iff p (target - p)).mp hppos
    apply (exactPrimePairFiber_nonempty_iff target).mpr
    exact ⟨p, target - p, hpq.1, hpq.2,
      Nat.add_sub_of_le (Nat.le_of_lt (Finset.mem_Ico.mp hpwindow).2)⟩
  · rw [exactPrimePairFiber_nonempty_iff]
    rintro ⟨p, q, hp, hq, hsum⟩
    have hpwindow : p ∈ Finset.Ico 1 target := by
      rw [Finset.mem_Ico]
      constructor
      · exact hp.one_le
      · rw [← hsum]
        exact Nat.lt_add_of_pos_right hq.pos
    refine ⟨p, hpwindow, ?_⟩
    have hsub : target - p = q := by
      rw [← hsum]
      exact Nat.add_sub_cancel_left p q
    rw [hsub]
    exact (primeIndicator_mul_pos_iff p q).mpr ⟨hp, hq⟩

/-! ## Von Mangoldt correlation and the prime-power boundary -/

/-- Ordered von Mangoldt Goldbach correlation on the same finite window. -/
def vonMangoldtGoldbachCorrelation (target : ℕ) : ℝ :=
  natPairCorrelation ArithmeticFunction.vonMangoldt target

/-- Ordered pair of prime powers. -/
structure PrimePowerPair where
  left : ℕ
  right : ℕ
  left_isPrimePow : IsPrimePow left
  right_isPrimePow : IsPrimePow right

def PrimePowerPair.energy (pair : PrimePowerPair) : ℕ :=
  pair.left + pair.right

/-- Exact additive fiber of ordered prime-power pairs. -/
def PrimePowerPairFiber (target : ℕ) :=
  { pair : PrimePowerPair // pair.energy = target }

/-- Full von Mangoldt positivity detects prime-power pairs, not necessarily
prime pairs. -/
theorem vonMangoldtGoldbachCorrelation_pos_iff_primePowerFiber
    (target : ℕ) :
    0 < vonMangoldtGoldbachCorrelation target ↔
      Nonempty (PrimePowerPairFiber target) := by
  rw [vonMangoldtGoldbachCorrelation, natPairCorrelation]
  rw [Finset.sum_pos_iff_of_nonneg]
  · constructor
    · rintro ⟨p, hpwindow, hppos⟩
      have hleft : 0 < ArithmeticFunction.vonMangoldt p :=
        pos_of_mul_pos_left hppos ArithmeticFunction.vonMangoldt_nonneg
      have hright : 0 < ArithmeticFunction.vonMangoldt (target - p) :=
        pos_of_mul_pos_right hppos ArithmeticFunction.vonMangoldt_nonneg
      refine ⟨⟨
        { left := p
          right := target - p
          left_isPrimePow := ArithmeticFunction.vonMangoldt_pos_iff.mp hleft
          right_isPrimePow := ArithmeticFunction.vonMangoldt_pos_iff.mp hright },
        ?_⟩⟩
      exact Nat.add_sub_of_le (Nat.le_of_lt (Finset.mem_Ico.mp hpwindow).2)
    · rintro ⟨⟨pair, henergy⟩⟩
      have hleftWindow : pair.left ∈ Finset.Ico 1 target := by
        rw [Finset.mem_Ico]
        constructor
        · exact pair.left_isPrimePow.pos
        · rw [← henergy]
          exact Nat.lt_add_of_pos_right pair.right_isPrimePow.pos
      refine ⟨pair.left, hleftWindow, ?_⟩
      have hsub : target - pair.left = pair.right := by
        rw [← henergy]
        exact Nat.add_sub_cancel_left pair.left pair.right
      rw [hsub]
      exact mul_pos
        (ArithmeticFunction.vonMangoldt_pos_iff.mpr pair.left_isPrimePow)
        (ArithmeticFunction.vonMangoldt_pos_iff.mpr pair.right_isPrimePow)
  · intro p _hp
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      ArithmeticFunction.vonMangoldt_nonneg

/-- Von Mangoldt weight restricted to actual primes. -/
def primeVonMangoldtWeight (n : ℕ) : ℝ :=
  if Nat.Prime n then ArithmeticFunction.vonMangoldt n else 0

@[simp] theorem primeVonMangoldtWeight_pos_iff (n : ℕ) :
    0 < primeVonMangoldtWeight n ↔ Nat.Prime n := by
  by_cases hn : Nat.Prime n
  · simp only [primeVonMangoldtWeight, if_pos hn]
    exact ⟨fun _ => hn,
      fun _ => ArithmeticFunction.vonMangoldt_pos_iff.mpr hn.isPrimePow⟩
  · simp [primeVonMangoldtWeight, hn]

theorem primeVonMangoldtWeight_nonneg (n : ℕ) :
    0 ≤ primeVonMangoldtWeight n := by
  by_cases hn : Nat.Prime n
  · simp [primeVonMangoldtWeight, hn,
      ArithmeticFunction.vonMangoldt_nonneg]
  · simp [primeVonMangoldtWeight, hn]

/-- Prime-only part of the von Mangoldt pair correlation. -/
def primeOnlyGoldbachCorrelation (target : ℕ) : ℝ :=
  natPairCorrelation primeVonMangoldtWeight target

/-- Prime-only weighted positivity is exactly exact prime-pair existence. -/
theorem primeOnlyGoldbachCorrelation_pos_iff (target : ℕ) :
    0 < primeOnlyGoldbachCorrelation target ↔
      Nonempty (ExactPrimePairFiber target) := by
  rw [primeOnlyGoldbachCorrelation, natPairCorrelation]
  rw [Finset.sum_pos_iff_of_nonneg]
  · constructor
    · rintro ⟨p, hpwindow, hppos⟩
      have hleft : 0 < primeVonMangoldtWeight p :=
        pos_of_mul_pos_left hppos (primeVonMangoldtWeight_nonneg _)
      have hright : 0 < primeVonMangoldtWeight (target - p) :=
        pos_of_mul_pos_right hppos (primeVonMangoldtWeight_nonneg _)
      apply (exactPrimePairFiber_nonempty_iff target).mpr
      exact ⟨p, target - p,
        (primeVonMangoldtWeight_pos_iff p).mp hleft,
        (primeVonMangoldtWeight_pos_iff (target - p)).mp hright,
        Nat.add_sub_of_le (Nat.le_of_lt (Finset.mem_Ico.mp hpwindow).2)⟩
    · rw [exactPrimePairFiber_nonempty_iff]
      rintro ⟨p, q, hp, hq, hsum⟩
      have hpwindow : p ∈ Finset.Ico 1 target := by
        rw [Finset.mem_Ico]
        exact ⟨hp.one_le, by rw [← hsum]; exact Nat.lt_add_of_pos_right hq.pos⟩
      refine ⟨p, hpwindow, ?_⟩
      have hsub : target - p = q := by
        rw [← hsum]
        exact Nat.add_sub_cancel_left p q
      rw [hsub]
      exact mul_pos
        ((primeVonMangoldtWeight_pos_iff p).mpr hp)
        ((primeVonMangoldtWeight_pos_iff q).mpr hq)
  · intro p _hp
    exact mul_nonneg (primeVonMangoldtWeight_nonneg p)
      (primeVonMangoldtWeight_nonneg (target - p))

/-- Contribution of pairs where at least one von Mangoldt-supported endpoint
is a proper prime power. -/
def primePowerCorrection (target : ℕ) : ℝ :=
  vonMangoldtGoldbachCorrelation target - primeOnlyGoldbachCorrelation target

theorem vonMangoldt_eq_primeOnly_add_primePowerCorrection (target : ℕ) :
    vonMangoldtGoldbachCorrelation target =
      primeOnlyGoldbachCorrelation target + primePowerCorrection target := by
  simp [primePowerCorrection]

/-- The full weighted correlation exceeds its prime-power correction exactly
when the exact prime-pair fiber is nonempty.  This is the safe bridge; mere
positivity of the full correlation only yields a prime-power pair. -/
theorem primePowerCorrection_lt_vonMangoldt_iff_exactPrimePair
    (target : ℕ) :
    primePowerCorrection target < vonMangoldtGoldbachCorrelation target ↔
      Nonempty (ExactPrimePairFiber target) := by
  rw [primePowerCorrection]
  have hiff :
      vonMangoldtGoldbachCorrelation target -
          primeOnlyGoldbachCorrelation target <
          vonMangoldtGoldbachCorrelation target ↔
        0 < primeOnlyGoldbachCorrelation target := by
    exact sub_lt_self_iff _
  exact hiff.trans (primeOnlyGoldbachCorrelation_pos_iff target)

end GoldbachPrimePairTrace
