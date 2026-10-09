import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Probability.Distributions.Gaussian.Real

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal Polynomial
noncomputable section

def g (v : ℝ) (t : ℝ) : ℝ := Real.exp (v*t^2/2)

def mgfPoly (v : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n+1 => (mgfPoly v n).derivative + C v * X * mgfPoly v n

theorem g_deriv (v : ℝ) : deriv (g v) = fun t => v*t*g v t := by
  funext t
  unfold g
  rw [_root_.deriv_exp (by fun_prop)]
  simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id,
    Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const',
    zero_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'',
    mul_one, zero_add]
  ring

theorem iterated_deriv_g (v : ℝ) (n : ℕ) :
    iteratedDeriv n (g v) = fun t => (mgfPoly v n).eval t * g v t := by
  induction n with
  | zero => simp [iteratedDeriv_zero,mgfPoly]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [deriv_fun_mul (by fun_prop) (by unfold g; fun_prop)]
      rw [Polynomial.deriv, congrFun (g_deriv v) t]
      simp [mgfPoly,eval_add,eval_mul]
      ring

theorem gauss_moment (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, x^n ∂gaussianReal 0 v) = (mgfPoly (v:ℝ) n).eval 0 := by
  have h := iteratedDeriv_mgf_zero
    (X := fun x : ℝ => x) (μ := gaussianReal 0 v) (by simp) n
  calc
    (∫ x : ℝ, x^n ∂gaussianReal 0 v) =
        iteratedDeriv n (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 := by
      simpa using h.symm
    _ = iteratedDeriv n (g (v:ℝ)) 0 := by
      rw [mgf_fun_id_gaussianReal]
      congr 1
      funext t
      simp [g]
    _ = _ := by
      rw [iterated_deriv_g]
      simp [g]

theorem poly_sixth (v : ℝ) : (mgfPoly v 6).eval 0 = 15*v^3 := by
  simp [mgfPoly]
  ring

theorem poly_eighth (v : ℝ) : (mgfPoly v 8).eval 0 = 105*v^4 := by
  simp [mgfPoly]
  ring

def gaussianMoment8 (n : ℕ) (v : ℝ) : ℝ :=
  if n = 0 then 1
  else if n = 2 then v
  else if n = 4 then 3*v^2
  else if n = 6 then 15*v^3
  else if n = 8 then 105*v^4
  else 0

theorem gaussian_moment_eight (n : ℕ) (v : ℝ≥0) (hn : n < 9) :
    (∫ x : ℝ, x^n ∂gaussianReal 0 v) =
      gaussianMoment8 n (v:ℝ) := by
  rw [gauss_moment]
  interval_cases n <;> simp [gaussianMoment8,mgfPoly] <;> ring

def rawMoment8 (n : ℕ) (b : ℝ) : ℝ :=
  gaussianMoment8 n (1/(2*b))*Real.sqrt (Real.pi/b)

theorem raw_moment_eight (n : ℕ) (b : ℝ)
    (hn : n < 9) (hb : 0 < b) :
    (∫ x : ℝ, x^n*Real.exp (-b*x^2)) = rawMoment8 n b := by
  let v : ℝ≥0 := ⟨1/(2*b), by positivity⟩
  have hvpos : 0 < (v:ℝ) := by
    change 0 < 1/(2*b)
    positivity
  have hv : v ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast hvpos
  have h := integral_gaussianReal_eq_integral_smul
    (μ := (0 : ℝ)) (v := v) (f := fun x : ℝ => x^n) hv
  rw [gaussian_moment_eight n v hn] at h
  have hpoint (x : ℝ) :
      gaussianPDFReal 0 v x * x^n =
        (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹ *
          (x^n * Real.exp (-b*x^2)) := by
    unfold gaussianPDFReal
    have hvval : (v:ℝ)=1/(2*b) := rfl
    rw [hvval]
    have expEq : -(x-0)^2/(2*(1/(2*b))) = -b*x^2 := by
      field_simp [ne_of_gt hb]
      ring
    rw [expEq]
    ring
  have hpdf :
      (∫ x : ℝ, gaussianPDFReal 0 v x * x^n) =
        gaussianMoment8 n (v:ℝ) := by
    simpa only [smul_eq_mul] using h.symm
  simp_rw [hpoint,integral_const_mul] at hpdf
  have hC : 0 < Real.sqrt (2*Real.pi*(v:ℝ)) := by
    apply Real.sqrt_pos.2
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) hvpos
  have hvval : (v:ℝ)=1/(2*b) := rfl
  rw [hvval] at hpdf hC
  have hroot : 2*Real.pi*(1/(2*b)) = Real.pi/b := by
    field_simp [ne_of_gt hb]
  rw [hroot] at hpdf hC
  unfold rawMoment8
  field_simp [ne_of_gt hC] at hpdf ⊢
  linarith

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
