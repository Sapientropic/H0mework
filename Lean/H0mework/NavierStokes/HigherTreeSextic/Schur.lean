import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedSchur
noncomputable section
variable {I : Type*}
abbrev Space (I : Type*) := lp (fun _ : I => ℝ) 2

variable (kernel : I → I → ℝ) (weight : I → ℝ) (cap : ℝ)
  (nonnegative : ∀ i j, 0 ≤ kernel i j) (positive : ∀ i, 0 < weight i) (cap0 : 0 ≤ cap)
  (rows : ∀ i (s : Finset I), (∑ j ∈ s, kernel i j*weight j) ≤ cap*weight i)
  (columns : ∀ j (s : Finset I), (∑ i ∈ s, kernel i j*weight i) ≤ cap*weight j)

def term (left right : Space I) (index : I × I) : ℝ :=
  kernel index.1 index.2 * |left index.1| * |right index.2|

include nonnegative in
theorem term_nonnegative (left right : Space I) (index : I × I) :
    0 ≤ term kernel left right index := by
  exact mul_nonneg (mul_nonneg (nonnegative _ _) (abs_nonneg _)) (abs_nonneg _)

theorem square_sum_le (value : Space I) (s : Finset I) :
    (∑ i ∈ s, |value i|^2) ≤ ‖value‖^2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs] using
    lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) value s

include nonnegative positive cap0 rows columns in
theorem rectangle_bound (left right : Space I) (s t : Finset I) :
    (∑ index ∈ s ×ˢ t, term kernel left right index) ≤ cap*‖left‖*‖right‖ := by
  let f : I × I → ℝ := fun index => kernel index.1 index.2*weight index.2/weight index.1*|left index.1|^2
  let g : I × I → ℝ := fun index => kernel index.1 index.2*weight index.1/weight index.2*|right index.2|^2
  have f0 (index : I × I) : 0 ≤ f index := by dsimp only [f]; positivity [nonnegative index.1 index.2, positive index.1, positive index.2]
  have g0 (index : I × I) : 0 ≤ g index := by dsimp only [g]; positivity [nonnegative index.1 index.2, positive index.1, positive index.2]
  have product (index : I × I) : (term kernel left right index)^2 ≤ f index*g index := by
    apply le_of_eq
    dsimp only [term, f, g]
    field_simp [(positive index.1).ne', (positive index.2).ne']
  have cauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s ×ˢ t)
    (fun index _ => f0 index) (fun index _ => g0 index) (fun index _ => product index)
  have first : (∑ index ∈ s ×ˢ t, f index) ≤ cap*‖left‖^2 := by
    rw [Finset.sum_product]
    calc
      _ = ∑ i ∈ s, (|left i|^2/weight i)*(∑ j ∈ t, kernel i j*weight j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [f]
        ring
      _ ≤ ∑ i ∈ s, (|left i|^2/weight i)*(cap*weight i) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (rows i t) (div_nonneg (sq_nonneg _) (positive i).le)
      _ = cap*(∑ i ∈ s, |left i|^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        field_simp [(positive i).ne']
      _ ≤ cap*‖left‖^2 := mul_le_mul_of_nonneg_left (square_sum_le left s) cap0
  have second : (∑ index ∈ s ×ˢ t, g index) ≤ cap*‖right‖^2 := by
    rw [Finset.sum_product, Finset.sum_comm]
    calc
      _ = ∑ j ∈ t, (|right j|^2/weight j)*(∑ i ∈ s, kernel i j*weight i) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [g]
        ring
      _ ≤ ∑ j ∈ t, (|right j|^2/weight j)*(cap*weight j) := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (columns j s) (div_nonneg (sq_nonneg _) (positive j).le)
      _ = cap*(∑ j ∈ t, |right j|^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        field_simp [(positive j).ne']
      _ ≤ cap*‖right‖^2 := mul_le_mul_of_nonneg_left (square_sum_le right t) cap0
  have square := cauchy.trans (mul_le_mul first second (Finset.sum_nonneg fun index _ => g0 index) (by positivity))
  have target0 : 0 ≤ cap*‖left‖*‖right‖ := by positivity
  nlinarith only [square, target0]

include nonnegative positive cap0 rows columns in
theorem finite_bound (left right : Space I) (s : Finset (I × I)) :
    (∑ index ∈ s, term kernel left right index) ≤ cap*‖left‖*‖right‖ := by
  classical
  apply le_trans _ (rectangle_bound kernel weight cap nonnegative positive cap0 rows columns left right
    (s.image Prod.fst) (s.image Prod.snd))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro index inside
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst inside, Finset.mem_image_of_mem Prod.snd inside⟩
  · intro index _ _
    exact term_nonnegative kernel nonnegative left right index

include nonnegative positive cap0 rows columns in
theorem summable (left right : Space I) : Summable (term kernel left right) :=
  summable_of_sum_le (term_nonnegative kernel nonnegative left right)
    (finite_bound kernel weight cap nonnegative positive cap0 rows columns left right)

include nonnegative positive cap0 rows columns in
theorem bound (left right : Space I) :
    (∑' index, term kernel left right index) ≤ cap*‖left‖*‖right‖ :=
  (summable kernel weight cap nonnegative positive cap0 rows columns left right).tsum_le_of_sum_le
    (finite_bound kernel weight cap nonnegative positive cap0 rows columns left right)

include nonnegative positive cap0 in
theorem of_tsum_rows
    (rowSummable : ∀ i, Summable (fun j => kernel i j*weight j))
    (rowBound : ∀ i, (∑' j, kernel i j*weight j) ≤ cap*weight i)
    (columnSummable : ∀ j, Summable (fun i => kernel i j*weight i))
    (columnBound : ∀ j, (∑' i, kernel i j*weight i) ≤ cap*weight j)
    (left right : Space I) :
    Summable (term kernel left right) ∧ (∑' index, term kernel left right index) ≤ cap*‖left‖*‖right‖ := by
  have rowFinite (i : I) (s : Finset I) : (∑ j ∈ s, kernel i j*weight j) ≤ cap*weight i :=
    ((rowSummable i).sum_le_tsum s (fun j _ => mul_nonneg (nonnegative i j) (positive j).le)).trans (rowBound i)
  have columnFinite (j : I) (s : Finset I) : (∑ i ∈ s, kernel i j*weight i) ≤ cap*weight j :=
    ((columnSummable j).sum_le_tsum s (fun i _ => mul_nonneg (nonnegative i j) (positive i).le)).trans (columnBound j)
  exact ⟨summable kernel weight cap nonnegative positive cap0 rowFinite columnFinite left right,
    bound kernel weight cap nonnegative positive cap0 rowFinite columnFinite left right⟩

end
end SaturationMonoid.NavierStokes.NativeUnheatedSchur
