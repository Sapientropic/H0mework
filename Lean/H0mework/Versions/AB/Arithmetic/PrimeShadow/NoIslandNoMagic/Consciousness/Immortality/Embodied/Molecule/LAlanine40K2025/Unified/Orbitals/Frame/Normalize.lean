import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Nondegenerate
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

def metricCorrection (G : Matrix n n ℝ) : Matrix n n ℝ := (CFC.sqrt G)⁻¹

theorem correction_gram (G : Matrix n n ℝ) (positive : G.PosDef) :
    (metricCorrection G).transpose * G * metricCorrection G = 1 := by
  have rootPositive : (CFC.sqrt G).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have rootUnit : IsUnit (CFC.sqrt G) := (CFC.isUnit_sqrt_iff G positive.posSemidef.nonneg).mpr positive.isUnit
  have invSym : (metricCorrection G).IsHermitian := rootPositive.isHermitian.inv
  have transpose : (metricCorrection G).transpose = metricCorrection G := by
    ext i j
    have entry := congrArg (fun M : Matrix n n ℝ => M i j) invSym.eq
    simpa only [Matrix.conjTranspose_apply,Matrix.transpose_apply,star_trivial] using entry
  rw [transpose]
  let := rootUnit.invertible
  calc
    _ = (CFC.sqrt G)⁻¹ * (CFC.sqrt G * CFC.sqrt G) * (CFC.sqrt G)⁻¹ := by
      rw [CFC.sqrt_mul_sqrt_self G positive.posSemidef.nonneg]
      rfl
    _ = 1 := by simp

def normalizedSourceFrame : Matrix Basis Basis ℝ := realInverse * metricCorrection actualGram

theorem normalized_original_metric (positive : actualGram.PosDef) :
    normalizedSourceFrame.transpose * originalMetric * normalizedSourceFrame = 1 := by
  rw [normalizedSourceFrame,Matrix.transpose_mul]
  calc
    _ = (metricCorrection actualGram).transpose * actualGram * metricCorrection actualGram := by
      simp only [actualGram,Matrix.mul_assoc]
    _ = 1 := correction_gram actualGram positive

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
