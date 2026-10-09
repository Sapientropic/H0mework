import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Dynamics.RaisingMoment

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.QuadraticEnergy

open Collision Load.Producer.HeatProbability
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped MatrixOrder in
theorem positive_energy (O rho : Matrix ι ι ℂ) (hO : O.PosSemidef) (hRho : rho.PosSemidef) :
    0 ≤ energy O rho := by
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hRho.nonneg
  rw [hD]
  have bound := (Complex.nonneg_iff.mp (hO.mul_mul_conjTranspose_same D).trace_nonneg).1
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm] at bound
  exact bound

abbrev operator (A : Matrix ι ι ℂ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A

theorem quadratic_read (F G : Matrix ι ι ℂ) (a : ℝ) (x : EuclideanSpace ℂ ι) :
    (inner ℂ (operator (Fᴴ * F - (a : ℂ) • (Gᴴ * G)) x) x).re =
      ‖operator F x‖ ^ 2 - a * ‖operator G x‖ ^ 2 := by
  simp only [operator, ← Matrix.star_eq_conjTranspose, map_sub, map_mul, map_smul, map_star,
    sub_apply, mul_apply_eq_comp, smul_apply, inner_sub_left,
    inner_smul_left, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_re, ← Complex.ofReal_pow]

theorem norm_domination_positive (F G : Matrix ι ι ℂ) (a : ℝ) (nonnegative : 0 ≤ a)
    (bound : ∀ x : EuclideanSpace ℂ ι, a * ‖operator G x‖ ≤ ‖operator F x‖) :
    (Fᴴ * F - (a ^ 2 : ℂ) • (Gᴴ * G)).PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  constructor
  · apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    apply (Matrix.isHermitian_conjTranspose_mul_self F).sub
    exact (Matrix.isHermitian_conjTranspose_mul_self G).smul
      (k := (a ^ 2 : ℂ)) (by simp [isSelfAdjoint_iff])
  · intro x
    change 0 ≤ (inner ℂ (operator (Fᴴ * F - (a ^ 2 : ℂ) • (Gᴴ * G)) x) x).re
    rw [← Complex.ofReal_pow, quadratic_read]
    have square := (sq_le_sq₀ (mul_nonneg nonnegative (norm_nonneg _)) (norm_nonneg _)).mpr (bound x)
    nlinarith

theorem norm_domination_energy (F G rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (a : ℝ) (nonnegative : 0 ≤ a)
    (bound : ∀ x : EuclideanSpace ℂ ι, a * ‖operator G x‖ ≤ ‖operator F x‖) :
    a ^ 2 * energy (Gᴴ * G) rho ≤ energy (Fᴴ * F) rho := by
  have lower := positive_energy _ rho (norm_domination_positive F G a nonnegative bound) positive
  rw [← Complex.ofReal_pow, energy_sub_left, energy_smul_left] at lower
  linarith

end
end LAlanine40K2025.Thermal.Recovery.QuadraticEnergy
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
