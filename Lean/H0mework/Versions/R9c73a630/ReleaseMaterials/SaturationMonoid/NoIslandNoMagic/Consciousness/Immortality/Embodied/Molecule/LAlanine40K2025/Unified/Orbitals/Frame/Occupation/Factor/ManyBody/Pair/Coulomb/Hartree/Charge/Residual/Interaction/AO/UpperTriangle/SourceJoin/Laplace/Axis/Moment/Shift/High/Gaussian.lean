import Mathlib.Probability.Distributions.Gaussian.Real
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second.Gaussian

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

private def g (v : ℝ) (t : ℝ) : ℝ := Real.exp (v*t^2/2)

private theorem d1 (v : ℝ) : deriv (g v) = fun t => v*t*g v t := by
  funext t
  unfold g
  rw [_root_.deriv_exp (by fun_prop)]
  simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id,
    Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const',
    zero_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'',
    mul_one, zero_add]
  ring

private theorem d2 (v : ℝ) :
    deriv (fun t => v*t*g v t) = fun t => (v+v^2*t^2)*g v t := by
  funext t
  rw [deriv_fun_mul (by fun_prop) (by unfold g; fun_prop)]
  rw [congrFun (d1 v) t]
  have hd : deriv (fun u : ℝ => v*u) t = v := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul v).deriv
  rw [hd]
  ring

private theorem d3 (v : ℝ) :
    deriv (fun t => (v+v^2*t^2)*g v t) =
      fun t => (3*v^2*t+v^3*t^3)*g v t := by
  funext t
  rw [deriv_fun_mul (by fun_prop) (by unfold g; fun_prop)]
  rw [congrFun (d1 v) t]
  have hd : deriv (fun u : ℝ => v+v^2*u^2) t = 2*v^2*t := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    simp only [deriv_const', zero_add]
    convert ((hasDerivAt_pow 2 t).const_mul (v^2)).deriv using 1; ring
  rw [hd]
  ring

private theorem d4 (v : ℝ) :
    deriv (fun t => (3*v^2*t+v^3*t^3)*g v t) =
      fun t => (3*v^2+6*v^3*t^2+v^4*t^4)*g v t := by
  funext t
  rw [deriv_fun_mul (by fun_prop) (by unfold g; fun_prop)]
  rw [congrFun (d1 v) t]
  have hd : deriv (fun u : ℝ => 3*v^2*u+v^3*u^3) t =
      3*v^2+3*v^3*t^2 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hfirst : deriv (fun u : ℝ => 3*v^2*u) t = 3*v^2 := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id t).const_mul (3*v^2)).deriv
    have hsecond : deriv (fun u : ℝ => v^3*u^3) t = 3*v^3*t^2 := by
      convert ((hasDerivAt_pow 3 t).const_mul (v^3)).deriv using 1; ring
    rw [hfirst,hsecond]
  rw [hd]
  ring

theorem gauss_fourth (v : ℝ≥0) :
    (∫ x : ℝ, x^4 ∂gaussianReal 0 v) = 3*(v:ℝ)^2 := by
  have h := iteratedDeriv_mgf_zero
    (X := fun x : ℝ => x) (μ := gaussianReal 0 v) (by simp) 4
  calc
    (∫ x : ℝ, x^4 ∂gaussianReal 0 v) =
        iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 := by
      simpa using h.symm
    _ = iteratedDeriv 4 (g (v:ℝ)) 0 := by
      rw [mgf_fun_id_gaussianReal]
      congr 1
      funext t
      simp [g]
    _ = 3*(v:ℝ)^2 := by
      simp only [iteratedDeriv_succ', iteratedDeriv_zero]
      rw [d1, d2, d3, d4]
      simp [g]

theorem gauss_third (v : ℝ≥0) :
    (∫ x : ℝ, x^3 ∂gaussianReal 0 v) = 0 := by
  have h := iteratedDeriv_mgf_zero
    (X := fun x : ℝ => x) (μ := gaussianReal 0 v) (by simp) 3
  calc
    (∫ x : ℝ, x^3 ∂gaussianReal 0 v) =
        iteratedDeriv 3 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 := by
      simpa using h.symm
    _ = iteratedDeriv 3 (g (v:ℝ)) 0 := by
      rw [mgf_fun_id_gaussianReal]
      congr 1
      funext t
      simp [g]
    _ = 0 := by
      simp only [iteratedDeriv_succ', iteratedDeriv_zero]
      rw [d1, d2, d3]
      simp [g]

theorem pdf_fourth (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ x : ℝ, gaussianPDFReal 0 v x * x^4) = 3*(v:ℝ)^2 := by
  have h := integral_gaussianReal_eq_integral_smul
    (μ := (0 : ℝ)) (v := v) (f := fun x : ℝ => x^4) hv
  rw [gauss_fourth] at h
  simpa only [smul_eq_mul] using h.symm

theorem gaussian_fourth_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => x^4 * Real.exp (-b*x^2)) := by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 4)

theorem gaussian_fourth_closed (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, x^4 * Real.exp (-b*x^2)) =
      3*(1/(2*b))^2 * Real.sqrt (Real.pi/b) := by
  let v : ℝ≥0 := ⟨1/(2*b), by positivity⟩
  have hvpos : 0 < (v:ℝ) := by
    change 0 < 1/(2*b)
    positivity
  have hv : v ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast hvpos
  have h := pdf_fourth v hv
  have hpoint (x : ℝ) :
      gaussianPDFReal 0 v x * x^4 =
        (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹ *
          (x^4 * Real.exp (-b*x^2)) := by
    unfold gaussianPDFReal
    have hvval : (v:ℝ)=1/(2*b) := rfl
    rw [hvval]
    have expEq : -(x-0)^2/(2*(1/(2*b))) = -b*x^2 := by
      field_simp [ne_of_gt hb]
      ring
    rw [expEq]
    ring
  simp_rw [hpoint,integral_const_mul] at h
  have hC : 0 < Real.sqrt (2*Real.pi*(v:ℝ)) := by
    apply Real.sqrt_pos.2
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) hvpos
  have hvval : (v:ℝ)=1/(2*b) := rfl
  rw [hvval] at h hC
  have hroot : 2*Real.pi*(1/(2*b)) = Real.pi/b := by
    field_simp [ne_of_gt hb]
  rw [hroot] at h hC
  field_simp [ne_of_gt hC] at h ⊢
  linarith

theorem gaussian_third_zero (b : ℝ) :
    (∫ x : ℝ, x^3 * Real.exp (-b*x^2)) = 0 := by
  let f : ℝ → ℝ := fun x => x^3 * Real.exp (-b*x^2)
  have h := Measure.integral_comp_mul_left f (-1 : ℝ)
  have hsame : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := by
    simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] using h
  have hodd : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    dsimp [f]
    have hs : (-x)^2 = x^2 := by ring
    rw [hs]
    ring
  simp_rw [hodd,integral_neg] at hsame
  change -(∫ x : ℝ, x^3 * Real.exp (-b*x^2)) = _ at hsame
  linarith

def rawMoment (n : ℕ) (b : ℝ) : ℝ :=
  if n = 0 then Real.sqrt (Real.pi/b)
  else if n = 1 then 0
  else if n = 2 then (1/(2*b))*Real.sqrt (Real.pi/b)
  else if n = 3 then 0
  else 3*(1/(2*b))^2*Real.sqrt (Real.pi/b)

theorem integrable_raw_monomial (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => x^n * Real.exp (-b*x^2)) := by
  have hs : (-1 : ℝ) < (n : ℝ) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (b := b) (s := (n : ℝ)) hb hs
  simpa only [Real.rpow_natCast] using h

theorem raw_moment_integral (n : ℕ) (b : ℝ)
    (hn : n < 5) (hb : 0 < b) :
    (∫ x : ℝ, x^n * Real.exp (-b*x^2)) = rawMoment n b := by
  interval_cases n
  · simp only [rawMoment, pow_zero, one_mul, ↓reduceIte]
    exact integral_gaussian b
  · simp only [rawMoment, pow_one, Nat.one_ne_zero, ↓reduceIte]
    exact Moment.gaussian_first_zero b
  · simpa [rawMoment] using Moment.Second.gaussian_second_simple b hb
  · simpa [rawMoment] using gaussian_third_zero b
  · simpa [rawMoment] using gaussian_fourth_closed b hb

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
