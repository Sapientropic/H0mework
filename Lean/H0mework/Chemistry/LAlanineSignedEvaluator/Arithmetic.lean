import H0mework.Chemistry.LAlanineExponential.RangeReduction

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedEvaluator

open SourceExponential

abbrev Pair := ℚ × ℚ

def Holds (a : Pair) (x : ℝ) : Prop := (a.1 : ℝ) ≤ x ∧ x ≤ (a.2 : ℝ)
def point (x : ℚ) : Pair := (roundDown x, roundUp x)
def add (a b : Pair) : Pair := (a.1 + b.1, a.2 + b.2)
def neg (a : Pair) : Pair := (-a.2, -a.1)
def sub (a b : Pair) : Pair := add a (neg b)
def lowerCorner (a b : Pair) : ℚ := min (min (a.1*b.1) (a.1*b.2)) (min (a.2*b.1) (a.2*b.2))
def upperCorner (a b : Pair) : ℚ := max (max (a.1*b.1) (a.1*b.2)) (max (a.2*b.1) (a.2*b.2))
def mul (a b : Pair) : Pair := (roundDown (lowerCorner a b), roundUp (upperCorner a b))
def square (a : Pair) : Pair :=
  (roundDown (if a.1 ≤ 0 ∧ 0 ≤ a.2 then 0 else min (a.1^2) (a.2^2)),
    roundUp (max (a.1^2) (a.2^2)))
def exponential (a : Pair) (kl kh : ℕ) : Pair := (leafLower a.1 kl, leafUpper a.2 kh)

theorem point_holds (x : ℚ) : Holds (point x) (x : ℝ) := by
  constructor
  · exact_mod_cast roundDown_le x
  · exact_mod_cast le_roundUp x

theorem add_holds (a b : Pair) (x y : ℝ) (ha : Holds a x) (hb : Holds b y) :
    Holds (add a b) (x+y) := by
  simpa only [Holds, add, Rat.cast_add] using And.intro (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)

theorem neg_holds (a : Pair) (x : ℝ) (ha : Holds a x) : Holds (neg a) (-x) := by
  simpa only [Holds, neg, Rat.cast_neg] using And.intro (neg_le_neg ha.2) (neg_le_neg ha.1)

theorem sub_holds (a b : Pair) (x y : ℝ) (ha : Holds a x) (hb : Holds b y) :
    Holds (sub a b) (x-y) := add_holds a (neg b) x (-y) ha (neg_holds b y hb)

private theorem linear_range (c l u x : ℝ) (hl : l ≤ x) (hu : x ≤ u) :
    min (c*l) (c*u) ≤ c*x ∧ c*x ≤ max (c*l) (c*u) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hl hc),
      (mul_le_mul_of_nonneg_left hu hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hu hc),
      (mul_le_mul_of_nonpos_left hl hc).trans (le_max_left _ _)⟩

theorem mul_holds (a b : Pair) (x y : ℝ) (ha : Holds a x) (hb : Holds b y) :
    Holds (mul a b) (x*y) := by
  have h0 := linear_range (a.1 : ℝ) b.1 b.2 y hb.1 hb.2
  have h1 := linear_range (a.2 : ℝ) b.1 b.2 y hb.1 hb.2
  have hx := linear_range y a.1 a.2 x ha.1 ha.2
  simp only [mul_comm y] at hx
  have lower : (lowerCorner a b : ℝ) ≤ x*y := by
    simpa only [lowerCorner, Rat.cast_min, Rat.cast_mul] using (min_le_min h0.1 h1.1).trans hx.1
  have upper : x*y ≤ (upperCorner a b : ℝ) := by
    simpa only [upperCorner, Rat.cast_max, Rat.cast_mul] using hx.2.trans (max_le_max h0.2 h1.2)
  constructor
  · have h : (roundDown (lowerCorner a b) : ℝ) ≤ (lowerCorner a b : ℝ) := by
      exact_mod_cast roundDown_le (lowerCorner a b)
    exact h.trans lower
  · have h : (upperCorner a b : ℝ) ≤ (roundUp (upperCorner a b) : ℝ) := by
      exact_mod_cast le_roundUp (upperCorner a b)
    exact upper.trans h

theorem square_holds (a : Pair) (x : ℝ) (ha : Holds a x) : Holds (square a) (x^2) := by
  have upper : x^2 ≤ max ((a.1 : ℝ)^2) ((a.2 : ℝ)^2) := by
    rcases le_total 0 x with hx | hx
    · exact (by nlinarith [ha.2] : x^2 ≤ (a.2 : ℝ)^2).trans (le_max_right _ _)
    · exact (by nlinarith [ha.1] : x^2 ≤ (a.1 : ℝ)^2).trans (le_max_left _ _)
  have lower : ((if a.1 ≤ 0 ∧ 0 ≤ a.2 then 0 else min (a.1^2) (a.2^2) : ℚ) : ℝ) ≤ x^2 := by
    split_ifs with h
    · simpa only [Rat.cast_zero] using sq_nonneg x
    · push Not at h
      rcases lt_or_ge 0 a.1 with hl | hl
      · have hreal : (0 : ℝ) < (a.1 : ℝ) := by exact_mod_cast hl
        have hsq : (a.1 : ℝ)^2 ≤ x^2 := by nlinarith [ha.1]
        simpa only [Rat.cast_min, Rat.cast_pow] using (min_le_left _ _).trans hsq
      · have hu := h hl
        have hreal : (a.2 : ℝ) < (0 : ℝ) := by exact_mod_cast hu
        have hsq : (a.2 : ℝ)^2 ≤ x^2 := by nlinarith [ha.2]
        simpa only [Rat.cast_min, Rat.cast_pow] using (min_le_right _ _).trans hsq
  constructor
  · have h : (roundDown (if a.1 ≤ 0 ∧ 0 ≤ a.2 then 0 else min (a.1^2) (a.2^2)) : ℝ) ≤
        ((if a.1 ≤ 0 ∧ 0 ≤ a.2 then 0 else min (a.1^2) (a.2^2) : ℚ) : ℝ) := by
      exact_mod_cast roundDown_le (if a.1 ≤ 0 ∧ 0 ≤ a.2 then 0 else min (a.1^2) (a.2^2))
    exact h.trans lower
  · have h : max ((a.1 : ℝ)^2) ((a.2 : ℝ)^2) ≤ (roundUp (max (a.1^2) (a.2^2)) : ℝ) := by
      have hq := le_roundUp (max (a.1^(2:ℕ)) (a.2^(2:ℕ)))
      exact_mod_cast hq
    exact upper.trans h

theorem exponential_holds (a : Pair) (kl kh : ℕ)
    (hl : |reducedArgument a.1 kl| ≤ 1/2) (hh : |reducedArgument a.2 kh| ≤ 1/2)
    (x : ℝ) (hx : Holds a x) : Holds (exponential a kl kh) (Real.exp x) :=
  interval_contains a.1 a.2 kl kh hl hh x hx.1 hx.2

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedEvaluator
