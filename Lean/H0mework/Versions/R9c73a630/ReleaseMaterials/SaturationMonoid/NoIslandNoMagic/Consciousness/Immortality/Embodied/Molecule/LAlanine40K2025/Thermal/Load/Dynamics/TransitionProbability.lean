import H0mework.Chemistry.LAlanineThermalLoad.EnergyNorm
import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalLoad.GeneratedControllerEnvironment

/-! # Full-state transition probabilities and certified perturbation error -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer.HeatProbability

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem energy_sub_left (A B rho : Matrix ι ι ℂ) :
    Collision.energy (A - B) rho = Collision.energy A rho - Collision.energy B rho := by
  simp only [Collision.energy, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]

omit [DecidableEq ι] in
theorem energy_add_right (A rho sigma : Matrix ι ι ℂ) :
    Collision.energy A (rho + sigma) = Collision.energy A rho + Collision.energy A sigma := by
  simp only [Collision.energy, Matrix.mul_add, Matrix.trace_add, Complex.add_re]

theorem energy_smul_right (A rho : Matrix ι ι ℂ) (a : ℝ) :
    Collision.energy A ((a : ℂ) • rho) = a * Collision.energy A rho := by
  simp [Collision.energy, Matrix.trace_smul, Complex.mul_re]

theorem energy_smul_left (A rho : Matrix ι ι ℂ) (a : ℝ) :
    Collision.energy ((a : ℂ) • A) rho = a * Collision.energy A rho := by
  simp [Collision.energy, Matrix.trace_smul, Complex.mul_re]

theorem squared_probability_error (F G rho : Matrix ι ι ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1)
    (t epsilon : ℝ) (ht : 0 ≤ t) (he : 0 ≤ epsilon)
    (hG : ‖G‖ ≤ t) (error : ‖F - G‖ ≤ epsilon) :
    |Collision.energy (star F * F) rho - Collision.energy (star G * G) rho| ≤
      epsilon * (2 * t + epsilon) := by
  have hF : ‖F‖ ≤ t + epsilon := by
    have triangle := norm_add_le (F - G) G
    rw [sub_add_cancel] at triangle
    linarith
  have split : star F * F - star G * G = star F * (F - G) + (star F - star G) * G := by
    noncomm_ring
  have bound : ‖star F * F - star G * G‖ ≤ epsilon * (2 * t + epsilon) := by
    rw [split]
    calc
      _ ≤ ‖star F * (F - G)‖ + ‖(star F - star G) * G‖ := norm_add_le _ _
      _ ≤ ‖F‖ * ‖F - G‖ + ‖F - G‖ * ‖G‖ := by
        simpa only [← star_sub, norm_star] using
          add_le_add (norm_mul_le (star F) (F - G)) (norm_mul_le (star F - star G) G)
      _ ≤ (t + epsilon) * epsilon + epsilon * t := by
        exact add_le_add
          (mul_le_mul hF error (norm_nonneg _) (by positivity))
          (mul_le_mul error hG (norm_nonneg _) he)
      _ = _ := by ring
  rw [← energy_sub_left]
  exact (StrictThermal.energy_abs_le_norm _ rho positive normalized).trans bound

def Q (e : Fin 2) : Matrix (ι × Fin 2) (ι × Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i.2 = e then 1 else 0)

omit [Fintype ι] in
theorem Q_star (e : Fin 2) : star (Q (ι := ι) e) = Q e := by
  simp [Q, Matrix.star_eq_conjTranspose]

theorem Q_sq (e : Fin 2) : Q (ι := ι) e * Q e = Q e := by
  rw [Q, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem Q_norm (e : Fin 2) : ‖Q (ι := ι) e‖ ≤ 1 := by
  rw [Q, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  split_ifs <;> simp

omit [Fintype ι] in
theorem Q_sum : Q (ι := ι) 0 + Q 1 = 1 := by
  rw [Q, Q, Matrix.diagonal_add, ← Matrix.diagonal_one]
  congr 1
  funext ⟨i, e⟩
  fin_cases e <;> norm_num

theorem Q_orthogonal (e f : Fin 2) (different : e ≠ f) : Q (ι := ι) e * Q f = 0 := by
  rw [Q, Q, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    split_ifs with hi hf
    · exact False.elim (different (hi.symm.trans hf))
    all_goals simp
  · simp [Matrix.diagonal_apply_ne _ h]

def tagged (rho : Matrix ι ι ℂ) (e : Fin 2) : Matrix (ι × Fin 2) (ι × Fin 2) ℂ :=
  Matrix.kronecker rho (Matrix.diagonal (fun a => if a = e then 1 else 0))

omit [DecidableEq ι] in
theorem tagged_positive (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) (e : Fin 2) :
    (tagged rho e).PosSemidef := by
  apply positive.kronecker
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro a
  split_ifs <;> simp

omit [DecidableEq ι] in
theorem tagged_trace (rho : Matrix ι ι ℂ) (normalized : rho.trace = 1) (e : Fin 2) :
    (tagged rho e).trace = 1 := by
  simp [tagged, Matrix.kronecker, Matrix.trace_kronecker, normalized, Matrix.trace_diagonal]

theorem Q_tagged (rho : Matrix ι ι ℂ) (e : Fin 2) : Q e * tagged rho e = tagged rho e := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Q, Matrix.diagonal_mul, tagged, Matrix.kronecker, Matrix.kroneckerMap_apply]
  by_cases ha : a = e
  · simp [ha]
  · by_cases hab : a = b
    · subst b; simp [ha]
    · simp [ha, hab]

theorem tagged_Q (rho : Matrix ι ι ℂ) (e : Fin 2) : tagged rho e * Q e = tagged rho e := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Q, Matrix.mul_diagonal, tagged, Matrix.kronecker, Matrix.kroneckerMap_apply]
  by_cases hb : b = e
  · simp [hb]
  · by_cases hab : a = b
    · subst b; simp [hb]
    · simp [hb, hab]

def flip (f : Fin 2) (A : Matrix (ι × Fin 2) (ι × Fin 2) ℂ) (e : Fin 2) := Q f * A * Q e

theorem compressed_norm (A : Matrix (ι × Fin 2) (ι × Fin 2) ℂ) (e f : Fin 2) :
    ‖flip f A e‖ ≤ ‖A‖ := by
  unfold flip
  calc
    _ ≤ ‖Q (ι := ι) f * A‖ * ‖Q (ι := ι) e‖ := norm_mul_le _ _
    _ ≤ (‖Q (ι := ι) f‖ * ‖A‖) * 1 := by
      exact mul_le_mul (norm_mul_le _ _) (Q_norm e) (norm_nonneg _) (by positivity)
    _ ≤ ‖A‖ := by nlinarith [Q_norm (ι := ι) f, norm_nonneg A]

omit [DecidableEq ι] in
theorem square_probability_trace (A rho : Matrix ι ι ℂ) :
    Collision.energy (star A * A) rho = (A * rho * star A).trace.re :=
  congrArg Complex.re (Matrix.trace_mul_cycle A rho (star A)).symm

theorem flip_probability (rho : Matrix ι ι ℂ)
    (U : Matrix (ι × Fin 2) (ι × Fin 2) ℂ) (e f : Fin 2) :
    Collision.energy (star (flip f U e) * flip f U e) (tagged rho e) =
      Collision.energy (Q f) (U * tagged rho e * star U) := by
  rw [square_probability_trace]
  have middle : Q e * tagged rho e * Q e = tagged rho e := by rw [Q_tagged, tagged_Q]
  have factor : flip f U e * tagged rho e * star (flip f U e) =
      Q f * (U * (Q e * tagged rho e * Q e) * star U) * Q f := by
    simp only [flip, star_mul, Q_star]
    noncomm_ring
  rw [factor, middle, Matrix.trace_mul_cycle, Q_sq]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem real_complex_smul (A : Matrix ι ι ℂ) (t : ℝ) :
    t • (-Complex.I • A) = (-Complex.I * (t : ℂ)) • A := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem reference_square (A : Matrix ι ι ℂ) (t : ℝ) :
    star ((-Complex.I * (t : ℂ)) • A) * ((-Complex.I * (t : ℂ)) • A) =
      ((t ^ 2 : ℝ) : ℂ) • (star A * A) := by
  rw [star_smul, smul_mul_smul_comm]
  congr 1
  simp only [star_mul, star_neg, Complex.star_def, Complex.conj_I,
    Complex.conj_ofReal, neg_neg, Complex.ofReal_pow]
  ring_nf
  simp [Complex.I_sq]

theorem flip_probability_error (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) (U W : Matrix (ι × Fin 2) (ι × Fin 2) ℂ)
    (t : ℝ) (ht : 0 ≤ t) (normW : ‖W‖ ≤ 1)
    (error : ‖U - 1 - t • (-Complex.I • W)‖ ≤ t / 4)
    (e f : Fin 2) (different : f ≠ e) :
    |Collision.energy (Q f) (U * tagged rho e * star U) -
      t ^ 2 * Collision.energy (star (flip f W e) * flip f W e) (tagged rho e)| ≤
        9 * t ^ 2 / 16 := by
  let F := flip f U e
  let G := (-Complex.I * (t : ℂ)) • flip f W e
  have gnorm : ‖G‖ ≤ t := by
    have contraction := (compressed_norm W e f).trans normW
    dsimp [G]
    rw [norm_smul]
    simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht, one_mul]
    nlinarith [norm_nonneg (flip f W e)]
  have errorIdentity : F - G = flip f (U - 1 - t • (-Complex.I • W)) e := by
    dsimp [F, G, flip]
    rw [real_complex_smul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mul_smul_comm,
      smul_mul_assoc, Q_orthogonal f e different, sub_zero]
  have flipError : ‖F - G‖ ≤ t / 4 := by
    rw [errorIdentity]
    exact (compressed_norm _ e f).trans error
  have squared := squared_probability_error F G (tagged rho e)
    (tagged_positive rho positive e) (tagged_trace rho normalized e)
    t (t / 4) ht (by positivity) gnorm flipError
  rw [show star G * G = ((t ^ 2 : ℝ) : ℂ) • (star (flip f W e) * flip f W e) from
    reference_square (flip f W e) t, energy_smul_left] at squared
  rw [show Collision.energy (star F * F) (tagged rho e) =
    Collision.energy (Q f) (U * tagged rho e * star U) from flip_probability rho U e f] at squared
  convert squared using 1; ring

end

end LAlanine40K2025.Thermal.Load.Producer.HeatProbability
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
