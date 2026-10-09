import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Dynamics.ProjectedProbability

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.ProbabilityComparison

open Collision Load.Producer.HeatProbability Load.Producer.StrictThermal
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem half_squared_lower (F G rho : Matrix ι ι ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (error : ‖F - G‖ ≤ epsilon) :
    energy (Gᴴ * G) rho / 2 - epsilon ^ 2 ≤ energy (Fᴴ * F) rho := by
  have identity : (2 : ℂ) • (Fᴴ * F) + (2 : ℂ) • ((F - G)ᴴ * (F - G)) - Gᴴ * G =
      ((2 : ℂ) • F - G)ᴴ * ((2 : ℂ) • F - G) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul]
    norm_num
    simp only [smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul]
    module
  have positiveGram := Moment.squared_energy_nonnegative ((2 : ℂ) • F - G) rho positive
  rw [← identity] at positiveGram
  have scalarized : 0 ≤ 2 * energy (Fᴴ * F) rho +
      2 * energy ((F - G)ᴴ * (F - G)) rho - energy (Gᴴ * G) rho := by
    simpa [energy, Matrix.add_mul, Matrix.sub_mul, Matrix.trace_smul, Complex.mul_re] using positiveGram
  have errorSquared : energy ((F - G)ᴴ * (F - G)) rho ≤ epsilon ^ 2 := by
    apply (le_abs_self _).trans ((energy_abs_le_norm _ rho positive normalized).trans _)
    calc
      _ ≤ ‖(F - G)ᴴ‖ * ‖F - G‖ := norm_mul_le _ _
      _ ≤ epsilon * epsilon := by
        rw [← Matrix.star_eq_conjTranspose, norm_star]
        exact mul_le_mul error error (norm_nonneg _) nonnegative
      _ = _ := (pow_two epsilon).symm
  linarith

theorem projection_energy (Q rho : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ)
    (hermitian : Q.IsHermitian) (idempotent : Q * Q = Q) :
    energy ((Q * (U : Matrix ι ι ℂ))ᴴ * (Q * (U : Matrix ι ι ℂ))) rho =
      energy Q (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U rho) := by
  have pulled := energy_pullback Q rho U
  simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at pulled ⊢
  rw [Matrix.conjTranspose_mul, hermitian.eq]
  simpa only [mul_assoc, ← mul_assoc Q Q, idempotent, Matrix.star_eq_conjTranspose] using pulled.symm

theorem unitary_error_lower (Q rho : Matrix ι ι ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1)
    (hermitian : Q.IsHermitian) (idempotent : Q * Q = Q) (contractive : ‖Q‖ ≤ 1)
    (U E : Matrix.unitaryGroup ι ℂ) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (error : ‖(E : Matrix ι ι ℂ) - 1‖ ≤ epsilon) :
    energy Q (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U rho) / 2 - epsilon ^ 2 ≤
      energy Q (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) (U * E) rho) := by
  have difference : Q * ((U * E : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) - Q * U =
      (Q * (U : Matrix ι ι ℂ)) * ((E : Matrix ι ι ℂ) - 1) := by
    simp only [MulMemClass.coe_mul, mul_sub, mul_one, mul_assoc]
  have bound : ‖Q * ((U * E : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) - Q * U‖ ≤ epsilon := by
    rw [difference]
    calc
      _ ≤ ‖Q * (U : Matrix ι ι ℂ)‖ * ‖(E : Matrix ι ι ℂ) - 1‖ := norm_mul_le _ _
      _ ≤ 1 * epsilon := by
        rw [CStarRing.norm_mul_coe_unitary]
        exact mul_le_mul contractive error (norm_nonneg _) zero_le_one
      _ = _ := one_mul epsilon
  have lower := half_squared_lower
    (Q * ((U * E : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)) (Q * U) rho
    positive normalized epsilon nonnegative bound
  rw [projection_energy Q rho U hermitian idempotent,
    projection_energy Q rho (U * E) hermitian idempotent] at lower
  exact lower

end
end LAlanine40K2025.Thermal.Recovery.ProbabilityComparison
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
