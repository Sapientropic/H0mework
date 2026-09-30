import H0mework.Chemistry.LAlanineSignedEvaluator.Gaussian
import H0mework.Chemistry.LAlanineRefinementDensity.DensityModel

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedEvaluator

open SourceGaussianModel SourceExponential
open scoped BigOperators

def midpoint (a : Pair) : ℚ := roundDown ((a.1+a.2)/2)
def radius (a : Pair) : ℚ := max (a.2-midpoint a) (midpoint a-a.1)
def productRadius (a b : Pair) : ℚ :=
  |midpoint a| * radius b + radius a * |midpoint b| + radius a * radius b

theorem deviation_le_radius (a : Pair) (x : ℝ) (hx : Holds a x) :
    |x-(midpoint a : ℝ)| ≤ (radius a : ℝ) := by
  rw [abs_le, radius, Rat.cast_max, Rat.cast_sub, Rat.cast_sub]
  have h0 := le_max_left ((a.2 : ℝ)-(midpoint a : ℝ)) ((midpoint a : ℝ)-(a.1 : ℝ))
  have h1 := le_max_right ((a.2 : ℝ)-(midpoint a : ℝ)) ((midpoint a : ℝ)-(a.1 : ℝ))
  constructor <;> linarith [hx.1, hx.2]

theorem product_deviation_le (a b : Pair) (x y : ℝ) (hx : Holds a x) (hy : Holds b y) :
    |x*y - (midpoint a : ℝ)*(midpoint b : ℝ)| ≤ (productRadius a b : ℝ) := by
  have ha := deviation_le_radius a x hx
  have hb := deviation_le_radius b y hy
  have raNonneg := (abs_nonneg _).trans ha
  have rbNonneg := (abs_nonneg _).trans hb
  have h0 : |(midpoint a : ℝ)*(y-midpoint b)| ≤ |(midpoint a : ℝ)| * (radius b : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  have h1 : |(x-midpoint a)*(midpoint b : ℝ)| ≤ (radius a : ℝ) * |(midpoint b : ℝ)| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have h2 : |(x-midpoint a)*(y-midpoint b)| ≤ (radius a : ℝ)*(radius b : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) raNonneg
  have he : x*y-(midpoint a : ℝ)*(midpoint b : ℝ) =
      ((midpoint a : ℝ)*(y-midpoint b) + (x-midpoint a)*(midpoint b : ℝ)) +
        (x-midpoint a)*(y-midpoint b) := by ring
  rw [he]
  simp only [productRadius, Rat.cast_add, Rat.cast_mul, Rat.cast_abs]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h0 h1)) h2)

section Finite
variable {Index : Type*} [Fintype Index]

/-- This is the source's midpoint-radius matrix dot, including its final outward rounding. -/
def dotCentre (a b : Index → Pair) : ℚ := ∑ i, midpoint (a i)*midpoint (b i)
def dotRadius (a b : Index → Pair) : ℚ := ∑ i, productRadius (a i) (b i)
def dotPair (a b : Index → Pair) : Pair :=
  (roundDown (dotCentre a b-dotRadius a b), roundUp (dotCentre a b+dotRadius a b))

theorem dotPair_contains (a b : Index → Pair) (x y : Index → ℝ)
    (hx : ∀ i, Holds (a i) (x i)) (hy : ∀ i, Holds (b i) (y i)) :
    Holds (dotPair a b) (∑ i, x i*y i) := by
  have h : |(∑ i, x i*y i) - (dotCentre a b : ℝ)| ≤ (dotRadius a b : ℝ) := by
    simp only [dotCentre, dotRadius, Rat.cast_sum, Rat.cast_mul, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => product_deviation_le (a i) (b i) (x i) (y i) (hx i) (hy i)))
  have hr := abs_le.mp h
  constructor
  · have rounding : (roundDown (dotCentre a b-dotRadius a b) : ℝ) ≤
        (dotCentre a b : ℝ)-(dotRadius a b : ℝ) := by
      have hq := roundDown_le (dotCentre a b-dotRadius a b)
      exact_mod_cast hq
    exact rounding.trans (by linarith [hr.1])
  · have rounding : (dotCentre a b : ℝ)+(dotRadius a b : ℝ) ≤
        (roundUp (dotCentre a b+dotRadius a b) : ℝ) := by
      have hq := le_roundUp (dotCentre a b+dotRadius a b)
      exact_mod_cast hq
    exact le_trans (by linarith [hr.2]) rounding

def firstMatrixPair (a : Index → Pair) (matrix : Index → Index → ℚ) (j : Index) : Pair :=
  dotPair a (fun i => point (matrix i j))

def bilinearPair (a b : Index → Pair) (matrix : Index → Index → ℚ) : Pair :=
  dotPair (firstMatrixPair a matrix) b

theorem bilinearPair_contains (a b : Index → Pair) (matrix : Index → Index → ℚ)
    (orbitals : Index → List Term) (left right : MultiIndex) (x : Point)
    (ha : ∀ i, Holds (a i) (orbital (orbitals i) left x))
    (hb : ∀ i, Holds (b i) (orbital (orbitals i) right x)) :
    Holds (bilinearPair a b matrix) (bilinear orbitals matrix left right x) := by
  have hfirst (j : Index) := dotPair_contains a (fun i => point (matrix i j))
    (fun i => orbital (orbitals i) left x) (fun i => (matrix i j : ℝ)) ha
      (fun i => point_holds (matrix i j))
  have h := dotPair_contains (firstMatrixPair a matrix) b
    (fun j => ∑ i, orbital (orbitals i) left x * (matrix i j : ℝ))
    (fun j => orbital (orbitals j) right x) hfirst hb
  have he : (∑ j, (∑ i, orbital (orbitals i) left x * (matrix i j : ℝ)) * orbital (orbitals j) right x) =
      bilinear orbitals matrix left right x := by
    simp only [bilinear, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [bilinearPair, he] using h

def rectangleBilinear (orbitals : Index → List Term) (matrix : Index → Index → ℚ)
    (left right : MultiIndex) (box : Rectangle) (steps : Term → ℕ × ℕ) : Pair :=
  bilinearPair (fun i => orbitalPair (orbitals i) left box steps)
    (fun i => orbitalPair (orbitals i) right box steps) matrix

theorem rectangleBilinear_contains (orbitals : Index → List Term) (matrix : Index → Index → ℚ)
    (left right : MultiIndex) (box : Rectangle) (steps : Term → ℕ × ℕ)
    (reduction : ∀ i, ∀ t ∈ orbitals i, TermReductionValid t box (steps t).1 (steps t).2)
    (x : Point) (hx : InRectangle box x) :
    Holds (rectangleBilinear orbitals matrix left right box steps) (bilinear orbitals matrix left right x) :=
  bilinearPair_contains _ _ matrix orbitals left right x
    (fun i => orbitalPair_contains (orbitals i) left box steps (reduction i) x hx)
    (fun i => orbitalPair_contains (orbitals i) right box steps (reduction i) x hx)

end Finite

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedEvaluator
