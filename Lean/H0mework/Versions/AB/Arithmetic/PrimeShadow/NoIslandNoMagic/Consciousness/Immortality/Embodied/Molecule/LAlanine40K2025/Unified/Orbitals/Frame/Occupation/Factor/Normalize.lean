import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Positive
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def correction : Matrix OccupiedSlot OccupiedSlot ℂ := (CFC.sqrt gram)⁻¹
def normalizedFactor : Matrix Basis OccupiedSlot ℂ := factor * correction

theorem correction_gram : star correction * gram * correction = 1 := by
  have rootPositive : (CFC.sqrt gram).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg gram)
  have rootUnit : IsUnit (CFC.sqrt gram) :=
    (CFC.isUnit_sqrt_iff gram gram_positive.posSemidef.nonneg).mpr gram_positive.isUnit
  have invHermitian : correction.IsHermitian := rootPositive.isHermitian.inv
  have starCorrection : star correction = correction := by
    simpa only [Matrix.star_eq_conjTranspose] using invHermitian.eq
  rw [starCorrection]
  let := rootUnit.invertible
  calc
    _ = (CFC.sqrt gram)⁻¹ * (CFC.sqrt gram * CFC.sqrt gram) * (CFC.sqrt gram)⁻¹ := by
      rw [CFC.sqrt_mul_sqrt_self gram gram_positive.posSemidef.nonneg]
      rfl
    _ = 1 := by simp

theorem normalized_isometry : normalizedFactor.conjTranspose * normalizedFactor = 1 := by
  rw [normalizedFactor,Matrix.conjTranspose_mul]
  calc
    correction.conjTranspose * factor.conjTranspose * (factor * correction) =
        correction.conjTranspose * (factor.conjTranspose * factor) * correction := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by simpa only [gram,Matrix.star_eq_conjTranspose] using correction_gram

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
