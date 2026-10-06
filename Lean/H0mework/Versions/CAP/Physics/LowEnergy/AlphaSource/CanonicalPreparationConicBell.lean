import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationConicNormalization
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumConicComposition
open scoped BigOperators ContDiff Topology

private theorem finite_order (n : ℕ) : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast (ENat.natCast_lt_top n).le

/-- The same actual chain-rule partitions, restricted by their outer derivative order. -/
def partialBell (G : ℕ → ℝ) (m k : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition m, if c.length=k then ∏ i, G (c.partSize i) else 0

def composeBound (O G : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m+1), O k*partialBell G m k

theorem partialBell_zero (G : ℕ → ℝ) (k : ℕ) :
    partialBell G 0 k=if k=0 then 1 else 0 := by
  classical
  simp [partialBell,OrderedFinpartition.default_eq,OrderedFinpartition.atomic,eq_comm]

theorem partialBell_above (G : ℕ → ℝ) (m k : ℕ) (above : m < k) :
    partialBell G m k=0 := by
  classical
  apply Finset.sum_eq_zero
  intro c _
  rw [if_neg (by have h := c.length_le; omega)]

theorem partialBell_nonnegative (G : ℕ → ℝ) (positive : ∀ j,0 ≤ G j) (m k : ℕ) :
    0 ≤ partialBell G m k := by
  classical
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact Finset.prod_nonneg (fun i _ => positive _)
  · exact le_rfl

private def jetPolynomial (G : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N+1), if j=0 then 0 else G j/(j.factorial : ℝ)*t^j

private theorem jetPolynomial_smooth (G : ℕ → ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (jetPolynomial G N) := by
  unfold jetPolynomial
  apply ContDiff.sum
  intro j _
  split_ifs
  · exact contDiff_const
  · exact contDiff_const.mul (contDiff_id.pow j)

private theorem jetPolynomial_zero (G : ℕ → ℝ) (N : ℕ) : jetPolynomial G N 0=0 := by
  classical
  unfold jetPolynomial
  apply Finset.sum_eq_zero
  intro j _
  by_cases zero : j=0
  · simp [zero]
  · simp [zero]

private theorem jetPolynomial_jet (G : ℕ → ℝ) (N j : ℕ) (positive : 0 < j) (within : j ≤ N) :
    iteratedDeriv j (jetPolynomial G N) 0=G j := by
  classical
  unfold jetPolynomial
  rw [iteratedDeriv_fun_sum]
  · have nonzero : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    rw [Finset.sum_eq_single j]
    · simp only [if_neg positive.ne']
      rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_pow_zero,if_pos rfl]
      field_simp
    · intro i hi different
      by_cases zero : i=0
      · subst i; simp
      · simp only [if_neg zero]
        rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_pow_zero,if_neg (Ne.symm different),Nat.cast_zero,mul_zero]
    · intro outside
      exact False.elim (outside (Finset.mem_range.mpr (by omega)))
  · intro i _
    split_ifs
    · exact contDiffAt_const
    · exact ((contDiff_const.mul (contDiff_id.pow i)).contDiffAt).of_le (finite_order j)

private def dividedPower (k : ℕ) (t : ℝ) : ℝ := t^k/(k.factorial : ℝ)

private theorem dividedPower_smooth (k : ℕ) : ContDiff ℝ ∞ (dividedPower k) := by
  exact (contDiff_id.pow k).div_const _

private theorem dividedPower_zero_jet (k j : ℕ) :
    iteratedDeriv j (dividedPower k) 0=if j=k then 1 else 0 := by
  unfold dividedPower
  rw [show (fun t : ℝ => t^k/(k.factorial : ℝ))=fun t => (k.factorial : ℝ)⁻¹*t^k by funext t; ring]
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_pow_zero]
  by_cases equal : j=k
  · subst j
    simp [k.factorial_ne_zero]
  · simp [equal]

private theorem polynomial_partition (G : ℕ → ℝ) (N m k : ℕ) (within : m ≤ N) :
    iteratedDeriv m (dividedPower k ∘ jetPolynomial G N) 0=partialBell G m k := by
  classical
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
    ((dividedPower_smooth k).contDiffAt) ((jetPolynomial_smooth G N).contDiffAt) (finite_order m)]
  simp only [jetPolynomial_zero,dividedPower_zero_jet]
  unfold partialBell
  apply Finset.sum_congr rfl
  intro c _
  by_cases length : c.length=k
  · rw [if_pos length,if_pos length,one_mul]
    apply Finset.prod_congr rfl
    intro i _
    exact jetPolynomial_jet G N _ (c.partSize_pos i) ((c.partSize_le i).trans within)
  · simp [length]

private theorem dividedPower_deriv (k : ℕ) (t : ℝ) :
    deriv (dividedPower (k+1)) t=dividedPower k t := by
  unfold dividedPower
  rw [deriv_div_const,deriv_pow_field,Nat.add_sub_cancel,
    Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp

/-- Full convolution form of the literal positive partial-Bell recurrence. -/
theorem partialBell_succ (G : ℕ → ℝ) (m k : ℕ) :
    partialBell G (m+1) (k+1)=
      ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ)*G (j+1)*partialBell G (m-j) k := by
  classical
  let h := jetPolynomial G (m+1)
  have dh : deriv (dividedPower (k+1) ∘ h)=deriv h*(dividedPower k ∘ h) := by
    funext t
    rw [deriv_comp t ((dividedPower_smooth (k+1)).differentiable (by simp) (h t))
      ((jetPolynomial_smooth G (m+1)).differentiable (by simp) t),dividedPower_deriv]
    exact mul_comm _ _
  rw [←polynomial_partition G (m+1) (m+1) (k+1) le_rfl,
    iteratedDeriv_succ',dh,iteratedDeriv_mul]
  · apply Finset.sum_congr rfl
    intro j hj
    have jle : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [←iteratedDeriv_succ',jetPolynomial_jet G (m+1) (j+1) (by omega) (by omega),
      polynomial_partition G (m+1) (m-j) k (by omega)]
  · exact (contDiff_infty_iff_deriv.mp (jetPolynomial_smooth G (m+1))).2.contDiffAt.of_le (finite_order m)
  · exact ((dividedPower_smooth k).comp (jetPolynomial_smooth G (m+1))).contDiffAt.of_le (finite_order m)

/-- Exactly the truncated convolution in the original Python compose_bounds loop. -/
theorem partialBell_literal (G : ℕ → ℝ) (m k : ℕ) :
    partialBell G (m+1) (k+1)=
      ∑ j ∈ Finset.range (m+1-k), (m.choose j : ℝ)*G (j+1)*partialBell G (m-j) k := by
  rw [partialBell_succ]
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j full outside
    have bound := Finset.mem_range.mp full
    have lower : m+1-k ≤ j := Nat.le_of_not_lt (by simpa only [Finset.mem_range] using outside)
    rw [partialBell_above G (m-j) k (by omega),mul_zero]

theorem composeBound_zero (O G : ℕ → ℝ) : composeBound O G 0=O 0 := by
  simp [composeBound,partialBell_zero]

end LowEnergy.PreparationVacuumConicComposition
