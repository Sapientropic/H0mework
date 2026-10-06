import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceRadiusPairedScalarPrice
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceRadiusBandPolynomial
open Finset

def band (m ell : ℕ) (q : ℝ) : ℝ := ∑ j ∈ Ico m ell,q^(j+1)
def slope (m ell : ℕ) (q : ℝ) : ℝ := ∑ j ∈ Ico m ell,(j+1 : ℝ)*q^j

private theorem cubic_choose (j : ℕ) : (j+1 : ℝ)^3 ≤ 6*((j+3).choose 3 : ℕ) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose j 3
  norm_num [Nat.ascFactorial_succ] at h
  have hh : (j+1 : ℝ)*(j+2)*(j+3)=6*((j+3).choose 3 : ℕ) := by
    have hn : (j+1)*(j+2)*(j+3)=6*(j+3).choose 3 := by nlinarith only [h]
    exact_mod_cast hn
  rw [←hh]
  have hj : 0≤(j : ℝ) := by positivity
  nlinarith

private theorem cubic_sum (q : ℝ) (hq : 0≤q) (hq1 : q<1) (t : Finset ℕ) :
    (1-q)^4*(∑ j ∈ t,(j+1 : ℝ)^3*q^j) ≤ 6 := by
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one 3
    (show ‖q‖<1 by simpa only [Real.norm_eq_abs,abs_of_nonneg hq] using hq1)
  have hb := sum_le_hasSum t (fun j _ => by positivity : ∀ j ∉ t,0≤((j+3).choose 3 : ℝ)*q^j) hs
  have hc : (∑ j ∈ t,(j+1 : ℝ)^3*q^j) ≤ 6*(∑ j ∈ t,((j+3).choose 3 : ℝ)*q^j) := by
    rw [Finset.mul_sum]
    exact sum_le_sum (fun j _ => by simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_right (cubic_choose j) (pow_nonneg hq j)))
  have hd : 0<(1-q)^4 := pow_pos (sub_pos.mpr hq1) _
  have ht := mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left hb (by norm_num))) hd.le
  have he : (1-q)^4*(6*(1/(1-q)^(3+1)))=6 := by field_simp
  exact ht.trans_eq he

/-- A finite geometric band's actual radial gradient is paid by the same band with a shrinking source coefficient. -/
theorem original_gradient_price (m ell : ℕ) (q : ℝ) (hq : 0≤q) (hq1 : q<1) :
    (m+1 : ℝ)*((1-q)^4*q*(2-q)/4*slope m ell q^2) ≤ 3*band m ell q := by
  let t := Ico m ell
  let U := ∑ j ∈ t,q^j
  let V := ∑ j ∈ t,(j+1 : ℝ)^2*q^j
  have hU : 0≤U := sum_nonneg (fun j _ => pow_nonneg hq j)
  have hV : 0≤V := sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (pow_nonneg hq j))
  have hc : slope m ell q^2 ≤ U*V := by
    exact sum_sq_le_sum_mul_sum_of_sq_le_mul t
      (r := fun j => (j+1 : ℝ)*q^j) (f := fun j => q^j) (g := fun j => (j+1 : ℝ)^2*q^j)
      (fun j _ => pow_nonneg hq j)
      (fun j _ => mul_nonneg (sq_nonneg _) (pow_nonneg hq j))
      (fun j _ => le_of_eq (by ring))
  have he : band m ell q=q*U := by
    simp only [band,U,t,Finset.mul_sum,pow_succ']
  have hn : (m+1 : ℝ)*V ≤ ∑ j ∈ t,(j+1 : ℝ)^3*q^j := by
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro j hj
    have hmj : (m+1 : ℝ)≤j+1 := by exact_mod_cast (Nat.add_le_add_right (mem_Ico.mp hj).1 1)
    have h := mul_le_mul_of_nonneg_right hmj (mul_nonneg (sq_nonneg (j+1 : ℝ)) (pow_nonneg hq j))
    exact h.trans_eq (by ring)
  have hmoment : (1-q)^4*((m+1 : ℝ)*V) ≤ 6 :=
    (mul_le_mul_of_nonneg_left hn (by positivity)).trans (cubic_sum q hq hq1 t)
  have htwo : 0≤2-q := by linarith
  have hfactor : 0≤(m+1 : ℝ)*(1-q)^4*q*(2-q)/4 := by positivity
  have hs := mul_le_mul_of_nonneg_left hc hfactor
  have hp := mul_le_mul_of_nonneg_left hmoment (show 0≤q*U*(2-q)/4 by positivity)
  have hqU : 0≤q*U := mul_nonneg hq hU
  rw [he]
  nlinarith only [hs,hp,hqU,mul_nonneg hq hqU]

end LowEnergy.SourceRadiusBandPolynomial
