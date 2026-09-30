import H0mework.NavierStokes.HigherTreeSextic.Schur

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedSchurThree
open NativeUnheatedSchur
noncomputable section
variable {I : Type*}
variable (profile : I → I → I → ℝ) (kernel : I → I → ℝ) (gain : ℝ)
  (profile0 : ∀ r b c, 0 ≤ profile r b c) (kernel0 : ∀ b c, 0 ≤ kernel b c) (gain0 : 0 ≤ gain)
  (squares : ∀ b c (s : Finset I), (∑ r ∈ s, (profile r b c)^2) ≤ (gain*kernel b c)^2)

include kernel0 gain0 squares in
theorem fiber_finite_bound (left : Space I) (b c : I) (s : Finset I) :
    (∑ r ∈ s, profile r b c * |left r|) ≤ gain*kernel b c*‖left‖ := by
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq s (fun r => profile r b c) (fun r => |left r|)
  have bounded := cauchy.trans (mul_le_mul (squares b c s) (square_sum_le left s)
    (Finset.sum_nonneg fun r _ => sq_nonneg _) (sq_nonneg _))
  have positive : 0 ≤ gain*kernel b c*‖left‖ := by positivity [kernel0 b c]
  nlinarith only [bounded, positive]

include profile0 kernel0 gain0 squares in
theorem fiber_summable (left : Space I) (b c : I) :
    Summable (fun r => profile r b c * |left r|) :=
  summable_of_sum_le (fun r => mul_nonneg (profile0 r b c) (abs_nonneg _))
    (fiber_finite_bound profile kernel gain kernel0 gain0 squares left b c)

include profile0 kernel0 gain0 squares in
theorem fiber_bound (left : Space I) (b c : I) :
    (∑' r, profile r b c * |left r|) ≤ gain*kernel b c*‖left‖ :=
  (fiber_summable profile kernel gain profile0 kernel0 gain0 squares left b c).tsum_le_of_sum_le
    (fiber_finite_bound profile kernel gain kernel0 gain0 squares left b c)

def term (left middle right : Space I) (index : (I × I) × I) : ℝ :=
  profile index.2 index.1.1 index.1.2 * |left index.2| * |middle index.1.1| * |right index.1.2|

include profile0 in
theorem term_nonnegative (left middle right : Space I) (index : (I × I) × I) :
    0 ≤ term profile left middle right index := by
  unfold term
  positivity [profile0 index.2 index.1.1 index.1.2]

include profile0 kernel0 gain0 squares in
theorem inner_summable (left middle right : Space I) (index : I × I) :
    Summable (fun r => term profile left middle right (index,r)) :=
  ((fiber_summable profile kernel gain profile0 kernel0 gain0 squares left index.1 index.2).mul_right
    |middle index.1|).mul_right |right index.2|

include profile0 kernel0 gain0 squares in
theorem inner_bound (left middle right : Space I) (index : I × I) :
    (∑' r, term profile left middle right (index,r)) ≤
      (gain*‖left‖)*NativeUnheatedSchur.term kernel middle right index := by
  change (∑' r, profile r index.1 index.2 * |left r| * |middle index.1| * |right index.2|) ≤ _
  rw [tsum_mul_right, tsum_mul_right]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (fiber_bound profile kernel gain profile0 kernel0 gain0 squares left index.1 index.2)
    (abs_nonneg (middle index.1))) (abs_nonneg (right index.2))).trans_eq (by unfold NativeUnheatedSchur.term; ring)

variable (weight : I → ℝ) (cap : ℝ) (positive : ∀ i, 0 < weight i) (cap0 : 0 ≤ cap)
  (rows : ∀ i (s : Finset I), (∑ j ∈ s, kernel i j*weight j) ≤ cap*weight i)
  (columns : ∀ j (s : Finset I), (∑ i ∈ s, kernel i j*weight i) ≤ cap*weight j)

include profile0 kernel0 gain0 squares positive cap0 rows columns in
theorem summable (left middle right : Space I) : Summable (term profile left middle right) := by
  apply (summable_prod_of_nonneg (term_nonnegative profile profile0 left middle right)).mpr
  refine ⟨inner_summable profile kernel gain profile0 kernel0 gain0 squares left middle right, ?_⟩
  apply ((NativeUnheatedSchur.summable kernel weight cap kernel0 positive cap0 rows columns middle right).mul_left
    (gain*‖left‖)).of_nonneg_of_le
  · intro index
    exact tsum_nonneg fun r => term_nonnegative profile profile0 left middle right (index,r)
  · exact inner_bound profile kernel gain profile0 kernel0 gain0 squares left middle right

include profile0 kernel0 gain0 squares positive cap0 rows columns in
theorem bound (left middle right : Space I) :
    (∑' index, term profile left middle right index) ≤ gain*cap*‖left‖*‖middle‖*‖right‖ := by
  have all := summable profile kernel gain profile0 kernel0 gain0 squares weight cap positive cap0 rows columns left middle right
  rw [all.tsum_prod]
  have compared := all.prod.tsum_le_tsum
    (inner_bound profile kernel gain profile0 kernel0 gain0 squares left middle right)
    ((NativeUnheatedSchur.summable kernel weight cap kernel0 positive cap0 rows columns middle right).mul_left (gain*‖left‖))
  rw [tsum_mul_left] at compared
  exact compared.trans ((mul_le_mul_of_nonneg_left
    (NativeUnheatedSchur.bound kernel weight cap kernel0 positive cap0 rows columns middle right)
    (mul_nonneg gain0 (norm_nonneg left))).trans_eq (by ring))

end
end SaturationMonoid.NavierStokes.NativeUnheatedSchurThree
