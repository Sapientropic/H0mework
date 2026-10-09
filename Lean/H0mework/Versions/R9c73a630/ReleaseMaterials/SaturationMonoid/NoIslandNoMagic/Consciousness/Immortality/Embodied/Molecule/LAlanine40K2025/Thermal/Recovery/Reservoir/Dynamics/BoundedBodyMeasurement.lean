import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Dynamics.QuadraticEnergy
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Measurement

open Collision Load.Producer.HeatProbability
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def measurementScale (A : Matrix ι ι ℂ) : ℝ := 1 + ‖A‖

theorem measurementScale_pos (A : Matrix ι ι ℂ) : 0 < measurementScale A := by
  unfold measurementScale
  positivity

def boundedEffect (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((1 / 2 : ℝ) : ℂ) • 1 + ((1 / (2 * measurementScale A) : ℝ) : ℂ) • A

theorem shifted_positive (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ((measurementScale A : ℂ) • (1 : Matrix ι ι ℂ) + A).PosSemidef := by
  have lower := hA.isSelfAdjoint.neg_algebraMap_norm_le_self
  have added : 0 ≤ algebraMap ℝ (Matrix ι ι ℂ) ‖A‖ + A := by
    simpa [add_comm] using add_le_add_left lower (algebraMap ℝ (Matrix ι ι ℂ) ‖A‖)
  have oneAdded := add_nonneg (show (0 : Matrix ι ι ℂ) ≤ 1 from zero_le_one) added
  apply Matrix.nonneg_iff_posSemidef.mp
  convert oneAdded using 1
  simp [measurementScale, Algebra.algebraMap_eq_smul_one, add_smul, add_assoc]

theorem boundedEffect_positive (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (boundedEffect A).PosSemidef := by
  have hM := measurementScale_pos A
  have hp := (shifted_positive A hA).smul
    (show (0 : ℂ) ≤ ((1 / (2 * measurementScale A) : ℝ) : ℂ) by
      exact_mod_cast (show (0 : ℝ) ≤ 1 / (2 * measurementScale A) by
        positivity))
  have product : (1 / (2 * measurementScale A) : ℝ) * measurementScale A = 1 / 2 := by
    field_simp
  have productC : ((1 / (2 * measurementScale A) : ℝ) : ℂ) * (measurementScale A : ℂ) =
      ((1 / 2 : ℝ) : ℂ) := by exact_mod_cast product
  simpa only [smul_add, smul_smul, productC, boundedEffect] using hp

theorem boundedEffect_complement (A : Matrix ι ι ℂ) :
    1 - boundedEffect A = boundedEffect (-A) := by
  simp only [boundedEffect, measurementScale, norm_neg, smul_neg]
  module

theorem boundedEffect_complement_positive (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (1 - boundedEffect A).PosSemidef := by
  rw [boundedEffect_complement]
  exact boundedEffect_positive (-A) hA.neg

theorem boundedEffect_read (A rho : Matrix ι ι ℂ) (normalized : rho.trace = 1) :
    energy (boundedEffect A) rho = 1 / 2 + energy A rho / (2 * measurementScale A) := by
  simp only [boundedEffect, energy, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_add, Matrix.trace_smul, normalized, smul_eq_mul, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, zero_mul, sub_zero]
  ring

theorem boundedEffect_probability (A rho : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    0 ≤ energy (boundedEffect A) rho ∧ energy (boundedEffect A) rho ≤ 1 := by
  refine ⟨QuadraticEnergy.positive_energy _ rho (boundedEffect_positive A hA) positive, ?_⟩
  have hc := QuadraticEnergy.positive_energy _ rho
    (boundedEffect_complement_positive A hA) positive
  rw [energy_sub_left] at hc
  have unit : energy (1 : Matrix ι ι ℂ) rho = 1 := by simp [energy, normalized]
  rw [unit] at hc
  linarith

def decodeMeasurement (A : Matrix ι ι ℂ) (z : ℝ) : ℝ :=
  2 * measurementScale A * (z - 1 / 2)

theorem decodeMeasurement_exact (A rho : Matrix ι ι ℂ) (normalized : rho.trace = 1) :
    decodeMeasurement A (energy (boundedEffect A) rho) = energy A rho := by
  rw [decodeMeasurement, boundedEffect_read A rho normalized]
  field_simp [(measurementScale_pos A).ne']
  ring

theorem decodeMeasurement_error (A rho : Matrix ι ι ℂ) (normalized : rho.trace = 1)
    (z eps : ℝ) (measured : |z - energy (boundedEffect A) rho| ≤ eps) :
    |decodeMeasurement A z - energy A rho| ≤ 2 * measurementScale A * eps := by
  rw [← decodeMeasurement_exact A rho normalized]
  have delta : decodeMeasurement A z - decodeMeasurement A (energy (boundedEffect A) rho) =
      2 * measurementScale A * (z - energy (boundedEffect A) rho) := by
    unfold decodeMeasurement
    ring
  rw [delta, abs_mul, abs_of_pos (mul_pos (by norm_num) (measurementScale_pos A))]
  exact mul_le_mul_of_nonneg_left measured
    (mul_nonneg (by norm_num) (measurementScale_pos A).le)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Measurement
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
