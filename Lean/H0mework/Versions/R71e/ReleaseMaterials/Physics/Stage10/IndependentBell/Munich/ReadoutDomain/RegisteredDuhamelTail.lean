import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace BellRegisteredDuhamel
noncomputable section

theorem difference_contraction {E : Type*} [SeminormedAddCommGroup E]
    (stay shift : E → E) (a : ℝ) (_ha : 0 ≤ a)
    (hs : ∀ x, ‖stay x‖ ≤ a*‖x‖) (ht : ∀ x, ‖shift x‖ ≤ a*‖x‖) (x : E) :
    ‖shift x-stay x‖ ≤ (2*a)*‖x‖ := by
  calc
    _ ≤ ‖shift x‖+‖stay x‖ := norm_sub_le _ _
    _ ≤ (2*a)*‖x‖ := by linarith [hs x, ht x]

theorem transfer_complement (loss detected : ℂ) (diagonal : ℂ)
    (h : loss+detected=diagonal) : loss=diagonal-detected := by
  linear_combination h

theorem source_recycle_split {E : Type*} [AddCommGroup E] [Module ℂ E]
    (image : E) (loss detected diagonal : ℂ) (h : loss+detected=diagonal) :
    loss • image = diagonal • image - detected • image := by
  rw [transfer_complement loss detected diagonal h, sub_smul]

def term (a : ℝ) (n : ℕ) : ℝ := a^n/(n.factorial : ℝ)

theorem term_nonnegative (a : ℝ) (n : ℕ) (ha : 0 ≤ a) : 0 ≤ term a n := by
  unfold term
  positivity

theorem term_successor (a : ℝ) (n : ℕ) :
    term a (n+1) = a/(n+1)*term a n := by
  simp only [term, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem suffix_geometric (a : ℝ) (N k : ℕ) (ha : 0 ≤ a) :
    term a (N+1+k) ≤ term a (N+1)*(a/(N+2))^k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show N+1+(k+1)=(N+1+k)+1 by omega, term_successor]
      have hd : (0 : ℝ) < N+2 := by positivity
      have hk : (N+2 : ℝ) ≤ (N+1+k : ℕ)+1 := by
        exact_mod_cast (show N+2 ≤ N+1+k+1 by omega)
      have hr : a/((N+1+k : ℕ)+1) ≤ a/(N+2) :=
        div_le_div_of_nonneg_left ha hd hk
      have hn := term_nonnegative a (N+1+k) ha
      have h0 : 0 ≤ a/(N+2) := by positivity
      calc
        _ ≤ (a/(N+2))*term a (N+1+k) := mul_le_mul_of_nonneg_right hr hn
        _ ≤ (a/(N+2))*(term a (N+1)*(a/(N+2))^k) := mul_le_mul_of_nonneg_left ih h0
        _ = _ := by rw [pow_succ]; ring

theorem geometric_telescopes (r : ℝ) (m : ℕ) :
    (1-r)*(∑ k ∈ Finset.range m, r^k) = 1-r^m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith

theorem geometric_sum_upper (r : ℝ) (m : ℕ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑ k ∈ Finset.range m, r^k) ≤ 1/(1-r) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-r)).mpr
  have h := geometric_telescopes r m
  have hn := pow_nonneg hr0 m
  nlinarith

theorem every_finite_suffix_upper (a : ℝ) (N m : ℕ) (ha : 0 ≤ a) (hsmall : a < N+2) :
    (∑ k ∈ Finset.range m, term a (N+1+k)) ≤
      term a (N+1)/(1-a/(N+2)) := by
  have hr0 : 0 ≤ a/(N+2) := by positivity
  have hr1 : a/(N+2) < 1 := (div_lt_one (by positivity : (0 : ℝ) < N+2)).mpr hsmall
  calc
    _ ≤ ∑ k ∈ Finset.range m, term a (N+1)*(a/(N+2))^k :=
      Finset.sum_le_sum fun k _ => suffix_geometric a N k ha
    _ = term a (N+1)*(∑ k ∈ Finset.range m, (a/(N+2))^k) := by rw [Finset.mul_sum]
    _ ≤ term a (N+1)*(1/(1-a/(N+2))) :=
      mul_le_mul_of_nonneg_left (geometric_sum_upper _ m hr0 hr1) (term_nonnegative a (N+1) ha)
    _ = _ := by ring

end
end BellRegisteredDuhamel
