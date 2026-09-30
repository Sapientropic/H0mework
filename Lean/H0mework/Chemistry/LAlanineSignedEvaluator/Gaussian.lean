import H0mework.Chemistry.LAlanineSignedEvaluator.Arithmetic
import H0mework.Chemistry.LAlanineRefinementDensity.GaussianCoefficients

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedEvaluator

open SourceGaussianModel GaussianCoefficients GaussianPrimitive SourceExponential
open scoped BigOperators

def horner (coefficients : ℕ → ℚ) : ℕ → Pair → Pair
  | 0, _ => point 0
  | n+1, a => add (mul (horner (fun i => coefficients (i+1)) n a) a) (point (coefficients 0))

theorem horner_contains (coefficients : ℕ → ℚ) (n : ℕ) (a : Pair) (x : ℝ) (hx : Holds a x) :
    Holds (horner coefficients n a) (∑ i ∈ Finset.range n, (coefficients i : ℝ) * x^i) := by
  induction n generalizing coefficients with
  | zero => simpa only [horner, Finset.range_zero, Finset.sum_empty, Rat.cast_zero] using point_holds 0
  | succ n ih =>
      have h := add_holds _ _ _ _
        (mul_holds _ _ _ _ (ih (fun i => coefficients (i+1))) hx) (point_holds (coefficients 0))
      have he : (∑ i ∈ Finset.range n, (coefficients (i+1) : ℝ) * x^i) * x + (coefficients 0 : ℝ) =
          ∑ i ∈ Finset.range (n+1), (coefficients i : ℝ) * x^i := by
        rw [Finset.sum_range_succ', Finset.sum_mul]
        simp only [pow_zero, mul_one, pow_succ, mul_assoc]
      simpa only [horner, he] using h

def jetHorner (alpha : ℚ) (power order : ℕ) (a : Pair) : Pair :=
  horner (jetCoeff alpha power order) (power+order+1) a

theorem jetHorner_contains (alpha : ℚ) (power order : ℕ) (a : Pair) (x : ℝ) (hx : Holds a x) :
    Holds (jetHorner alpha power order a) (((jetPoly alpha power order).map (algebraMap ℚ ℝ)).eval x) := by
  have degree : (jetPoly alpha power order).natDegree < power+order+1 :=
    Nat.lt_succ_of_le (jetPoly_degree alpha power order)
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range' (algebraMap ℚ ℝ) degree]
  have cast (q : ℚ) : algebraMap ℚ ℝ q = (q : ℝ) := by
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℝ) q
  simpa only [jetHorner, jetPoly_coeff, cast] using
    horner_contains (jetCoeff alpha power order) (power+order+1) a x hx

abbrev Rectangle := Fin 3 → Pair
def InRectangle (box : Rectangle) (x : Point) : Prop := ∀ axis, Holds (box axis) (x axis)
def relative (term : Term) (box : Rectangle) (axis : Fin 3) : Pair := sub (box axis) (point (term.centre axis))
def radialPair (term : Term) (box : Rectangle) : Pair :=
  mul (neg (point term.exponent))
    (add (add (add (point 0) (square (relative term box 0))) (square (relative term box 1)))
      (square (relative term box 2)))

noncomputable def radialArgument (term : Term) (x : Point) : ℝ :=
  -(term.exponent : ℝ) * ((x 0-term.centre 0)^2 + (x 1-term.centre 1)^2 + (x 2-term.centre 2)^2)

theorem relative_contains (term : Term) (box : Rectangle) (x : Point) (hx : InRectangle box x) (axis : Fin 3) :
    Holds (relative term box axis) (x axis - (term.centre axis : ℝ)) :=
  sub_holds _ _ _ _ (hx axis) (point_holds (term.centre axis))

theorem radialPair_contains (term : Term) (box : Rectangle) (x : Point) (hx : InRectangle box x) :
    Holds (radialPair term box) (radialArgument term x) := by
  have hp (axis : Fin 3) := square_holds _ _ (relative_contains term box x hx axis)
  have hs := add_holds _ _ _ _ (add_holds _ _ _ _
    (add_holds _ _ _ _ (point_holds 0) (hp 0)) (hp 1)) (hp 2)
  simpa only [radialPair, radialArgument, Rat.cast_zero, zero_add] using
    mul_holds _ _ _ _ (neg_holds _ _ (point_holds term.exponent)) hs

def termPair (term : Term) (d : MultiIndex) (box : Rectangle) (kl kh : ℕ) : Pair :=
  mul (mul (mul (mul (point term.weight) (exponential (radialPair term box) kl kh))
    (jetHorner term.exponent (term.powers 0) (d 0) (relative term box 0)))
      (jetHorner term.exponent (term.powers 1) (d 1) (relative term box 1)))
        (jetHorner term.exponent (term.powers 2) (d 2) (relative term box 2))

theorem value_shared_exponential (term : Term) (d : MultiIndex) (x : Point) :
    value term d x = (term.weight : ℝ) * Real.exp (radialArgument term x) *
      ((jetPoly term.exponent (term.powers 0) (d 0)).map (algebraMap ℚ ℝ)).eval (x 0-term.centre 0) *
      ((jetPoly term.exponent (term.powers 1) (d 1)).map (algebraMap ℚ ℝ)).eval (x 1-term.centre 1) *
      ((jetPoly term.exponent (term.powers 2) (d 2)).map (algebraMap ℚ ℝ)).eval (x 2-term.centre 2) := by
  have he : radialArgument term x =
      (-(term.exponent : ℝ)*(x 0-term.centre 0)^2 + -(term.exponent : ℝ)*(x 1-term.centre 1)^2) +
        -(term.exponent : ℝ)*(x 2-term.centre 2)^2 := by unfold radialArgument; ring
  rw [he, Real.exp_add, Real.exp_add]
  simp only [value, factor, gaussian]
  ring

def TermReductionValid (term : Term) (box : Rectangle) (kl kh : ℕ) : Prop :=
  |reducedArgument (radialPair term box).1 kl| ≤ 1/2 ∧
    |reducedArgument (radialPair term box).2 kh| ≤ 1/2

theorem termPair_contains (term : Term) (d : MultiIndex) (box : Rectangle) (kl kh : ℕ)
    (reduction : TermReductionValid term box kl kh) (x : Point) (hx : InRectangle box x) :
    Holds (termPair term d box kl kh) (value term d x) := by
  have he := exponential_holds (radialPair term box) kl kh reduction.1 reduction.2
    (radialArgument term x) (radialPair_contains term box x hx)
  have hp (axis : Fin 3) := jetHorner_contains term.exponent (term.powers axis) (d axis)
    (relative term box axis) (x axis-term.centre axis) (relative_contains term box x hx axis)
  rw [value_shared_exponential]
  exact mul_holds _ _ _ _ (mul_holds _ _ _ _ (mul_holds _ _ _ _
    (mul_holds _ _ _ _ (point_holds term.weight) he) (hp 0)) (hp 1)) (hp 2)

def orbitalPair (terms : List Term) (d : MultiIndex) (box : Rectangle) (steps : Term → ℕ × ℕ) : Pair :=
  (terms.map (fun t => termPair t d box (steps t).1 (steps t).2)).foldr add (point 0)

theorem orbitalPair_contains (terms : List Term) (d : MultiIndex) (box : Rectangle) (steps : Term → ℕ × ℕ)
    (reduction : ∀ t ∈ terms, TermReductionValid t box (steps t).1 (steps t).2)
    (x : Point) (hx : InRectangle box x) : Holds (orbitalPair terms d box steps) (orbital terms d x) := by
  induction terms with
  | nil => simpa only [orbitalPair, orbital, List.map_nil, List.foldr_nil, List.sum_nil, Rat.cast_zero] using point_holds 0
  | cons t rest ih =>
      have ht := termPair_contains t d box (steps t).1 (steps t).2 (reduction t (by simp)) x hx
      have hr := ih (fun s hs => reduction s (by simp [hs]))
      simpa only [orbitalPair, orbital, List.map_cons, List.foldr_cons, List.sum_cons] using add_holds _ _ _ _ ht hr

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedEvaluator
