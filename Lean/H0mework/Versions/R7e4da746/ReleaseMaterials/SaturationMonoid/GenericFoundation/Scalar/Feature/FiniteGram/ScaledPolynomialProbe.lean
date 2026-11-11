import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPolynomialProbe

open Finset Polynomial
open scoped Polynomial

def node {count : Nat} (i : Fin count) : ℝ :=
  (i.val : ℝ)+1

/-- Fixed interpolation weights for a coefficient of a polynomial sampled on a scaled grid. -/
def weight (count slot : Nat) (i : Fin count) : ℂ :=
  (Lagrange.basis univ (fun j : Fin count => (node j : ℂ)) i).coeff slot

def extract (count slot : Nat) (sample : Fin count → ℂ) : ℂ :=
  ∑ i, weight count slot i * sample i

def weightMass (count slot : Nat) : ℝ :=
  ∑ i, ‖weight count slot i‖

private theorem node_ge_one {count : Nat} (i : Fin count) : 1 ≤ node i := by
  exact le_add_of_nonneg_left (Nat.cast_nonneg i.val)

private theorem node_injective (count : Nat) : Function.Injective (fun i : Fin count => (node i : ℂ)) := by
  intro i j same
  apply Fin.ext
  have equal : (i.val : ℝ)+1 = (j.val : ℝ)+1 := Complex.ofReal_injective same
  exact_mod_cast add_right_cancel equal

theorem extract_scaled (count slot : Nat) (p : ℂ[X]) (degree : p.degree < count)
    (scale : ℝ) (positive : 0 < scale) :
    extract count slot (fun i => p.eval ((scale*node i : ℝ) : ℂ)) =
      p.coeff slot * (scale:ℂ)^slot := by
  let stretch : ℂ[X] := C (scale:ℂ)*X
  have oneDegree : stretch.degree = 1 := by
    unfold stretch
    rw [degree_C_mul (Complex.ofReal_ne_zero.mpr positive.ne'), degree_X]
  let q := p.comp stretch
  have small : q.degree < (univ : Finset (Fin count)).card := by
    change (p.comp stretch).degree < _
    rw [degree_comp (by rw [oneDegree]; exact zero_lt_one),oneDegree,mul_one,card_univ,Fintype.card_fin]
    exact degree
  have formula := Lagrange.eq_interpolate (f := q) (node_injective count).injOn small
  rw [Lagrange.interpolate_apply] at formula
  have atSlot := congrArg (fun u : ℂ[X] => u.coeff slot) formula
  simp only [q,stretch,comp_C_mul_X_coeff,finsetSum_coeff,coeff_C_mul,
    eval_comp,eval_mul,eval_C,eval_X] at atSlot
  simp only [extract,weight,Complex.ofReal_mul,atSlot]
  apply sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem norm_extract_le (count slot : Nat) (f : Fin count → ℂ) (bound : ℝ)
    (small : ∀ i, ‖f i‖ ≤ bound) :
    ‖extract count slot f‖ ≤ weightMass count slot * bound := by
  calc
    _ ≤ ∑ i, ‖weight count slot i * f i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖weight count slot i‖ * bound := by
      apply sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (small i) (norm_nonneg _)
    _ = _ := (sum_mul _ _ _).symm

private theorem weightMass_nonneg (count slot : Nat) : 0 ≤ weightMass count slot :=
  sum_nonneg fun _ _ => norm_nonneg _

private theorem exp_power_bound (power : Nat) {delay x : ℝ} (delayPos : 0 < delay) (xPos : 0 < x) :
    x^power * Real.exp (-x*delay) ≤ ((power+1).factorial : ℝ)/(delay^(power+1)*x) := by
  have factorPos : 0 < ((power+1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (power+1)
  have prodPos := mul_pos xPos delayPos
  have paid := (div_le_iff₀ factorPos).mp (Real.pow_div_factorial_le_exp (x*delay) prodPos.le (power+1))
  have inverse : Real.exp (-x*delay) ≤ ((power+1).factorial : ℝ)/(x*delay)^(power+1) := by
    rw [neg_mul,Real.exp_neg]
    apply (le_div_iff₀ (pow_pos prodPos _)).mpr
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using paid)
  calc
    _ ≤ x^power * (((power+1).factorial : ℝ)/(x*delay)^(power+1)) :=
      mul_le_mul_of_nonneg_left inverse (pow_nonneg xPos.le _)
    _ = _ := by
      rw [mul_pow, pow_succ x]
      field_simp [xPos.ne',delayPos.ne']

private def residualBudget (power : Nat) (amplitude delay : ℝ) : ℝ :=
  amplitude * ((power+1).factorial : ℝ) / delay^(power+1)

/-- The nonzero coefficient and a source decay budget determine a finite probe scale. -/
def scale (power slot : Nat) (amplitude delay : ℝ) (opening : ℂ) : ℝ :=
  1 + 2 * (weightMass (power+1) slot * residualBudget power amplitude delay) / ‖opening‖

theorem scale_ge_one (power slot : Nat) {amplitude delay : ℝ}
    (nonnegative : 0 ≤ amplitude) (positive : 0 < delay) (opening : ℂ) :
    1 ≤ scale power slot amplitude delay opening := by
  have mass := weightMass_nonneg (power+1) slot
  unfold scale residualBudget
  exact le_add_of_nonneg_right (by positivity)

private theorem tail_at_scale (power : Nat) {amplitude delay L x : ℝ}
    (amp : 0 ≤ amplitude) (positive : 0 < delay) (one : 1 ≤ L) (above : L ≤ x)
    (f : ℝ → ℂ) (decays : ∀ y, 1 ≤ y → ‖f y‖ ≤ amplitude*y^power*Real.exp (-y*delay)) :
    ‖f x‖ ≤ residualBudget power amplitude delay / L := by
  have LPos : 0 < L := zero_lt_one.trans_le one
  have xPos : 0 < x := LPos.trans_le above
  have point := exp_power_bound power positive xPos
  calc
    _ ≤ amplitude*(x^power*Real.exp (-x*delay)) := by
      rw [← mul_assoc]
      exact decays x (one.trans above)
    _ ≤ amplitude * (((power+1).factorial : ℝ)/(delay^(power+1)*x)) :=
      mul_le_mul_of_nonneg_left point amp
    _ = residualBudget power amplitude delay / x := by unfold residualBudget; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left _ LPos above
      unfold residualBudget
      positivity

/-- The weighted residual retains half the source coefficient against a decaying tail. -/
theorem finite_residue_margin (power slot : Nat) (p : ℂ[X]) (degree : p.degree < power+1)
    (opening : p.coeff slot ≠ 0) (amplitude delay : ℝ) (amp : 0 ≤ amplitude) (delayPos : 0 < delay)
    (tail : ℝ → ℂ) (decays : ∀ x, 1 ≤ x → ‖tail x‖ ≤ amplitude*x^power*Real.exp (-x*delay)) :
    let L := scale power slot amplitude delay (p.coeff slot)
    ‖p.coeff slot‖/2 ≤
      ‖extract (power+1) slot (fun i => tail (L*node i) - p.eval ((L*node i : ℝ) : ℂ))‖ := by
  let L := scale power slot amplitude delay (p.coeff slot)
  let mass := weightMass (power+1) slot
  let budget := residualBudget power amplitude delay
  have one := scale_ge_one power slot amp delayPos (p.coeff slot)
  have LPos : 0 < L := zero_lt_one.trans_le one
  have live : 0 < ‖p.coeff slot‖ := norm_pos_iff.mpr opening
  have margin : mass*budget/L ≤ ‖p.coeff slot‖/2 := by
    apply (div_le_iff₀ LPos).mpr
    change mass*budget ≤ ‖p.coeff slot‖/2*(1+2*(mass*budget)/‖p.coeff slot‖)
    field_simp [live.ne']
    nlinarith
  have bound (i : Fin (power+1)) : ‖tail (L*node i)‖ ≤ budget/L :=
    tail_at_scale power amp delayPos one
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (node_ge_one i) LPos.le) tail decays
  let y := extract (power+1) slot (fun i => tail (L*node i))
  have small : ‖y‖ ≤ ‖p.coeff slot‖/2 := by
    have localBound := norm_extract_le (power+1) slot _ _ bound
    exact (localBound.trans_eq (by change mass*(budget/L)=mass*budget/L; ring)).trans margin
  let z := extract (power+1) slot (fun i => p.eval ((L*node i : ℝ) : ℂ))
  have big : ‖p.coeff slot‖ ≤ ‖z‖ := by
    unfold z
    rw [extract_scaled (power+1) slot p (by exact_mod_cast degree) L LPos,
      norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos LPos]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ one) (norm_nonneg (p.coeff slot))
  have split : extract (power+1) slot (fun i => tail (L*node i)-p.eval ((L*node i : ℝ) : ℂ)) = y-z := by
    simp only [extract,y,z,mul_sub,sum_sub_distrib]
  change ‖p.coeff slot‖/2 ≤ ‖extract (power+1) slot _‖
  rw [split, norm_sub_rev y z]
  linarith [norm_sub_norm_le z y]

end SourceGeneratedPolynomialProbe
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
