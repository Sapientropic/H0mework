import H0mework.Chemistry.LAlanineBandGlobalSource.Orbital
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource

open SourceGaussianModel Filter
open scoped BigOperators Topology
noncomputable section

theorem pi_norm_sq_le_sum_sq (x : Point) : ‖x‖ ^ 2 ≤ ∑ i : Fin 3, x i ^ 2 := by
  have positive : 0 ≤ ∑ i : Fin 3, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have bound : ‖x‖ ≤ Real.sqrt (∑ i : Fin 3, x i ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
  nlinarith [Real.sq_sqrt positive, Real.sqrt_nonneg (∑ i : Fin 3, x i ^ 2), norm_nonneg x]

def termCentre (term : Term) : Point := fun i => (term.centre i : ℝ)

theorem term_gaussian_tail (term : Term) (positive : 0 < term.exponent) (d : MultiIndex) (x : Point) :
    |value term d x| ≤ (termBound term d : ℝ) *
      Real.exp (-((term.exponent : ℝ) / 2) * ‖x - termCentre term‖ ^ 2) := by
  let a : ℝ := (term.exponent : ℝ) / 2
  have ha : 0 < a := by dsimp [a]; exact div_pos (by exact_mod_cast positive) (by norm_num)
  have each (i : Fin 3) := gaussian_tail (by exact_mod_cast positive : (0 : ℝ) < (term.exponent : ℝ))
    ((jetPoly term.exponent (term.powers i) (d i)).map (algebraMap ℚ ℝ)) (x i - (term.centre i : ℝ))
  have product : |value term d x| ≤ |(term.weight : ℝ)| *
      ((factorBound term.exponent (term.powers 0) (d 0) : ℝ) * Real.exp (-a * (x 0 - (term.centre 0 : ℝ)) ^ 2)) *
      ((factorBound term.exponent (term.powers 1) (d 1) : ℝ) * Real.exp (-a * (x 1 - (term.centre 1 : ℝ)) ^ 2)) *
      ((factorBound term.exponent (term.powers 2) (d 2) : ℝ) * Real.exp (-a * (x 2 - (term.centre 2 : ℝ)) ^ 2)) := by
    simp only [value, abs_mul]
    exact mul_le_mul (mul_le_mul
      (mul_le_mul_of_nonneg_left (each 0) (abs_nonneg _))
      (each 1) (abs_nonneg _) (by positivity)) (each 2) (abs_nonneg _) (by positivity)
  have collected : |value term d x| ≤ (termBound term d : ℝ) *
      Real.exp (-a * (∑ i : Fin 3, (x i - (term.centre i : ℝ)) ^ 2)) := by
    convert product using 1
    simp only [termBound, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs,
      Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      Fin.sum_univ_zero, add_zero]
    rw [mul_add, mul_add, Real.exp_add, Real.exp_add]
    ring
  apply collected.trans
  apply mul_le_mul_of_nonneg_left _ (termBound term d).coe_nonneg
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (pi_norm_sq_le_sum_sq (x - termCentre term)) (by linarith)

theorem centred_gaussian_vanishes (centre : Point) (a : ℝ) (positive : 0 < a) :
    Tendsto (fun x : Point => Real.exp (-a * ‖x - centre‖ ^ 2)) (cocompact Point) (𝓝 0) := by
  have lower : Tendsto (fun x : Point => ‖x‖ - ‖centre‖) (cocompact Point) atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right (cocompact Point) (-‖centre‖) tendsto_norm_cocompact_atTop
  have far : Tendsto (fun x : Point => ‖x - centre‖) (cocompact Point) atTop :=
    tendsto_atTop_mono (fun x => norm_sub_norm_le x centre) lower
  exact Real.tendsto_exp_atBot.comp
    (((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp far).const_mul_atTop_of_neg (by linarith))

theorem term_vanishes (term : Term) (positive : 0 < term.exponent) (d : MultiIndex) :
    Tendsto (value term d) (cocompact Point) (𝓝 0) := by
  apply squeeze_zero_norm
    (fun x => by simpa only [Real.norm_eq_abs] using term_gaussian_tail term positive d x)
  simpa only [mul_zero] using
    (centred_gaussian_vanishes (termCentre term) ((term.exponent : ℝ) / 2)
      (by exact_mod_cast (div_pos positive (by norm_num : (0 : ℚ) < 2)))).const_mul (termBound term d : ℝ)

end
end LAlanine40K2025.BasinRefinement.GlobalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
