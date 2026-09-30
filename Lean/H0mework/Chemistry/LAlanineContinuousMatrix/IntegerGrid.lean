import H0mework.Chemistry.LAlanineSignedEvaluator.Contraction

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerGrid

open SourceSignedEvaluator SourceExponential
open scoped BigOperators

abbrev Interval := ℤ × ℤ
def denominator : ℕ := 2 ^ 160
def grid (a : Interval) : Pair := ((a.1 : ℚ) / scale, (a.2 : ℚ) / scale)
def mid (a : Interval) : ℤ := (a.1 + a.2) / 2
def rad (a : Interval) : ℤ := max (a.2 - mid a) (mid a - a.1)
def productRad (a b : Interval) : ℤ :=
  |mid a| * rad b + rad a * |mid b| + rad a * rad b

theorem denominator_cast : (denominator : ℚ) = scale := by
  norm_num [denominator, scale]

theorem grid_midpoint (a : Interval) : SourceSignedEvaluator.midpoint (grid a) = (mid a : ℚ) / scale := by
  have hs : scale ≠ 0 := ne_of_gt scale_positive
  unfold SourceSignedEvaluator.midpoint grid roundDown mid
  have h : scale * (((a.1 : ℚ) / scale + (a.2 : ℚ) / scale) / 2) =
      ((a.1 + a.2 : ℤ) : ℚ) / (2 : ℕ) := by push_cast; field_simp
  rw [h, Rat.floor_intCast_div_natCast]
  rfl

theorem grid_radius (a : Interval) : radius (grid a) = (rad a : ℚ) / scale := by
  rw [radius, grid_midpoint]
  simp only [grid, rad, Int.cast_max, Int.cast_sub]
  rw [← sub_div, ← sub_div, max_div_div_right scale_positive.le]

theorem grid_productRadius (a b : Interval) :
    productRadius (grid a) (grid b) = (productRad a b : ℚ) / scale ^ 2 := by
  simp only [productRadius, grid_midpoint, grid_radius, productRad,
    Int.cast_add, Int.cast_mul, Int.cast_abs, abs_div, abs_of_pos scale_positive]
  ring

theorem roundDown_square_grid (n : ℤ) :
    roundDown ((n : ℚ) / scale ^ 2) = ((n / (denominator : ℤ) : ℤ) : ℚ) / scale := by
  have hs : scale ≠ 0 := ne_of_gt scale_positive
  unfold roundDown
  have h : scale * ((n : ℚ) / scale ^ 2) = (n : ℚ) / (denominator : ℕ) := by
    rw [denominator_cast]
    field_simp
  rw [h, Rat.floor_intCast_div_natCast]

theorem roundUp_square_grid (n : ℤ) :
    roundUp ((n : ℚ) / scale ^ 2) = ((-((-n) / (denominator : ℤ)) : ℤ) : ℚ) / scale := by
  have hs : scale ≠ 0 := ne_of_gt scale_positive
  unfold roundUp
  have h : scale * ((n : ℚ) / scale ^ 2) = (n : ℚ) / (denominator : ℕ) := by
    rw [denominator_cast]
    field_simp
  rw [h, Rat.ceil_intCast_div_natCast]

section Finite
variable {Index : Type*} [Fintype Index]

def centre (a b : Index → Interval) : ℤ := ∑ i, mid (a i) * mid (b i)
def radiusSum (a b : Index → Interval) : ℤ := ∑ i, productRad (a i) (b i)
def dot (a b : Index → Interval) : Interval :=
  ((centre a b - radiusSum a b) / denominator,
    -((-(centre a b + radiusSum a b)) / denominator))

theorem centre_cast (a b : Index → Interval) :
    dotCentre (fun i => grid (a i)) (fun i => grid (b i)) =
      (centre a b : ℚ) / scale ^ 2 := by
  simp only [dotCentre, grid_midpoint, centre, Int.cast_sum, Int.cast_mul,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem radiusSum_cast (a b : Index → Interval) :
    dotRadius (fun i => grid (a i)) (fun i => grid (b i)) =
      (radiusSum a b : ℚ) / scale ^ 2 := by
  simp only [dotRadius, grid_productRadius, radiusSum, Int.cast_sum, Finset.sum_div]

/-- Integer evaluation is an exact normal form of the source's rounded signed dot. -/
theorem dot_commutes (a b : Index → Interval) :
    grid (dot a b) = dotPair (fun i => grid (a i)) (fun i => grid (b i)) := by
  unfold dotPair
  rw [centre_cast, radiusSum_cast, ← sub_div, ← add_div,
    ← Int.cast_sub, ← Int.cast_add, roundDown_square_grid, roundUp_square_grid]
  rfl

end Finite

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerGrid
