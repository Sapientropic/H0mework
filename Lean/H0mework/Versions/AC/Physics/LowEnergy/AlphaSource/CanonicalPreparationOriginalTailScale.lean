import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalRadius
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumOriginalRadii
open PreparationVacuumCentralBudget PreparationVacuumArenaRows
open scoped BigOperators Topology

-- The exact original upper_product algorithm bounds the two actual Leibniz folds.
theorem localizedCutoff_bound (B : ℕ → Fin 5 → ArrayBound) (theta radial : ArrayBound)
    (positiveB : ∀ k i m,0 ≤ B k i m) (positiveTheta : ∀ m,0 ≤ theta m)
    (positiveRadial : ∀ m,0 ≤ radial m) (k m : ℕ) (i : Fin 5) :
    productArray (productArray (B k i) theta) radial m≤
      exponentValue (localizedCutoff B theta radial k m) := by
  have first (n : ℕ) : productArray (B k i) theta n≤
      exponentValue (upperProduct (coefficientEnvelope B k) (fun a=>roundExponent (theta a)) n) := by
    calc
      _≤productArray (fun a=>exponentValue (coefficientEnvelope B k a))
          (fun a=>exponentValue (roundExponent (theta a))) n := by
        unfold productArray
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (coefficientEnvelope_bound B positiveB k a i) (Nat.cast_nonneg _)
        · exact roundExponent_upper _ (positiveTheta _)
        · exact positiveTheta _
        · exact mul_nonneg (Nat.cast_nonneg _) (exponentValue_nonnegative _)
      _≤_:=upperProduct_bound _ _ n
  calc
    _≤productArray
        (fun a=>exponentValue (upperProduct (coefficientEnvelope B k) (fun n=>roundExponent (theta n)) a))
        (fun a=>exponentValue (roundExponent (radial a))) m := by
      unfold productArray
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (first a) (Nat.cast_nonneg _)
      · exact roundExponent_upper _ (positiveRadial _)
      · exact positiveRadial _
      · exact mul_nonneg (Nat.cast_nonneg _) (exponentValue_nonnegative _)
    _≤_:=upperProduct_bound _ _ m

theorem source_radius_scaled_bound (cutoff : ℕ → UpperArray) (k m N : ℕ)
    (later : N<k) (order : m≤k) (r : ℝ) (outside : originalRadius cutoff k≤r) :
    exponentValue (cutoff k m)/r^(k-N)≤(1/2 : ℝ)^k := by
  have rp : 0<originalRadius cutoff k:=originalRadius_positive cutoff k
  have rpositive : 0<r:=rp.trans_le outside
  have rone : 1≤r:=by
    have lower:=(originalRadius_order cutoff k).trans outside
    exact (one_le_pow₀ (by norm_num : (1 : ℝ)≤2)).trans lower
  have degree : 1≤k-N:=by omega
  have power : r≤r^(k-N) := by
    have monotone:=pow_le_pow_right₀ rone degree
    simpa only [pow_one] using monotone
  have source:=(originalRadius_dyadic_bound cutoff k m (by omega) order)
  apply (div_le_iff₀ (pow_pos rpositive _)).mpr
  calc
    _≤originalRadius cutoff k*(1/2 : ℝ)^k:=source
    _≤r^(k-N)*(1/2 : ℝ)^k:=mul_le_mul_of_nonneg_right (outside.trans power) (by positivity)
    _=_:=mul_comm _ _

theorem source_radius_error_bound (cutoff : ℕ → UpperArray) (k m N : ℕ)
    (later : N<k) (order : m≤k) (r error : ℝ) (outside : originalRadius cutoff k≤r)
    (actual : |error|≤exponentValue (cutoff k m)/r^(k-N)) :
    |error|≤(1/2 : ℝ)^k := actual.trans (source_radius_scaled_bound cutoff k m N later order r outside)

theorem originalRadius_at_least_linear (cutoff : ℕ → UpperArray) (k : ℕ) :
    (k : ℝ)+1≤originalRadius cutoff k := by
  have powers : ∀ n : ℕ,(n : ℝ)+1≤(2 : ℝ)^n := by
    intro n
    induction n with
    | zero=>norm_num
    | succ n ih=>
      rw [pow_succ]
      push_cast
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ)≤2) n]
  exact (powers k).trans (originalRadius_order cutoff k)

/-- Rk≥2^k pays local finiteness at each finite physical radial momentum. -/
theorem originalRadius_finite_active (cutoff : ℕ → UpperArray) (r : ℝ) :
    Set.Finite {k : ℕ | originalRadius cutoff k≤r} := by
  apply (Set.finite_Iic ⌈r⌉₊).subset
  intro k hk
  have linear:=(originalRadius_at_least_linear cutoff k).trans hk
  have real : (k : ℝ)≤r:=by linarith
  exact_mod_cast real.trans (Nat.le_ceil r)

theorem shifted_geometric_hasSum (K : ℕ) :
    HasSum (fun j : ℕ=>(1/2 : ℝ)^(K+j)) (2*(1/2 : ℝ)^K) := by
  have initial:=hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<1)
  have result:=initial.mul_left ((1/2 : ℝ)^K)
  simpa only [←pow_add,show (1-(1/2 : ℝ))⁻¹=2 by norm_num,mul_comm] using result

/-- A single finite tail bound applies to every actual parameter satisfying the paid source estimate. -/
theorem originalRadius_finite_tail (cutoff : ℕ → UpperArray) (m N K L : ℕ)
    (lower : max m (N+1)≤K) (radius error : ℕ → ℝ)
    (outside : ∀ k∈Finset.range L,originalRadius cutoff (K+k)≤radius (K+k))
    (actual : ∀ k∈Finset.range L,|error (K+k)|≤
      exponentValue (cutoff (K+k) m)/(radius (K+k))^(K+k-N)) :
    |∑ k∈Finset.range L,error (K+k)|≤2*(1/2 : ℝ)^K := by
  have term (k : ℕ) (hk : k∈Finset.range L) : |error (K+k)|≤(1/2 : ℝ)^(K+k) := by
    apply source_radius_error_bound cutoff (K+k) m N (by omega) (by omega) _ _ (outside k hk) (actual k hk)
  calc
    _≤∑ k∈Finset.range L,|error (K+k)|:=Finset.abs_sum_le_sum_abs _ _
    _≤∑ k∈Finset.range L,(1/2 : ℝ)^(K+k):=Finset.sum_le_sum term
    _≤∑' k : ℕ,(1/2 : ℝ)^(K+k):=
      (shifted_geometric_hasSum K).summable.sum_le_tsum (Finset.range L) (by intro k _;positivity)
    _=2*(1/2 : ℝ)^K:=(shifted_geometric_hasSum K).tsum_eq

theorem originalRadius_tail_tends_zero :
    Filter.Tendsto (fun K : ℕ=>2*(1/2 : ℝ)^K) Filter.atTop (𝓝 0) := by
  have limit:=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<1)
  simpa only [mul_zero] using limit.const_mul 2

end LowEnergy.PreparationVacuumOriginalRadii
