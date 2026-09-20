import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Registered positive preparation, without identifying it with its input matrix -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Preparation

noncomputable section

open scoped ComplexOrder

variable {ι : Type*} [Fintype ι]

def gram (amplitude : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  amplitude * amplitude.conjTranspose

def gramMass (amplitude : Matrix ι ι ℂ) : ℝ :=
  (gram amplitude).trace.re

def normalizedGram (amplitude : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (gramMass amplitude)⁻¹ • gram amplitude

theorem gram_posSemidef (amplitude : Matrix ι ι ℂ) : (gram amplitude).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose amplitude

theorem gramMass_nonnegative (amplitude : Matrix ι ι ℂ) : 0 ≤ gramMass amplitude :=
  (Complex.nonneg_iff.mp (gram_posSemidef amplitude).trace_nonneg).1

theorem gram_trace (amplitude : Matrix ι ι ℂ) :
    (gram amplitude).trace = (gramMass amplitude : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (gram_posSemidef amplitude).trace_nonneg).2.symm

theorem gramMass_positive (amplitude : Matrix ι ι ℂ) (hne : amplitude ≠ 0) :
    0 < gramMass amplitude := by
  refine lt_of_le_of_ne (gramMass_nonnegative amplitude) ?_
  intro hzero
  apply hne
  apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
  change (gram amplitude).trace = 0
  rw [gram_trace, ← hzero]
  rfl

theorem normalizedGram_posSemidef (amplitude : Matrix ι ι ℂ) :
    (normalizedGram amplitude).PosSemidef :=
  (gram_posSemidef amplitude).smul (inv_nonneg.mpr (gramMass_nonnegative amplitude))

theorem normalizedGram_trace (amplitude : Matrix ι ι ℂ) (hne : amplitude ≠ 0) :
    (normalizedGram amplitude).trace = 1 := by
  rw [normalizedGram, Matrix.trace_smul, gram_trace]
  simp only [Complex.real_smul, Complex.ofReal_inv]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (gramMass_positive amplitude hne)))

variable [DecidableEq ι]

theorem unitary_conjugation_trace (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * A * star (U : Matrix ι ι ℂ)).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

theorem gram_conjugation (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    gram ((U : Matrix ι ι ℂ) * A * star (U : Matrix ι ι ℂ)) =
      (U : Matrix ι ι ℂ) * gram A * star (U : Matrix ι ι ℂ) := by
  simp only [gram, ← Matrix.star_eq_conjTranspose, star_mul, star_star]
  simp only [mul_assoc, ← mul_assoc (star (U : Matrix ι ι ℂ)) (U : Matrix ι ι ℂ),
    Unitary.coe_star_mul_self, one_mul]

theorem normalizedGram_conjugation (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    normalizedGram ((U : Matrix ι ι ℂ) * A * star (U : Matrix ι ι ℂ)) =
      (U : Matrix ι ι ℂ) * normalizedGram A * star (U : Matrix ι ι ℂ) := by
  have mass : gramMass ((U : Matrix ι ι ℂ) * A * star (U : Matrix ι ι ℂ)) = gramMass A := by
    rw [gramMass, gram_conjugation, unitary_conjugation_trace]
    rfl
  rw [normalizedGram, mass, gram_conjugation, normalizedGram]
  simp only [mul_smul_comm, smul_mul_assoc]

end

end LAlanine40K2025.Thermal.Preparation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
