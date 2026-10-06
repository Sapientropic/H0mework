import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Bounds
import Mathlib.LinearAlgebra.Matrix.Gershgorin

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open Propagation.Interface
open scoped Matrix ComplexOrder BigOperators
noncomputable section

def factor : Matrix Basis OccupiedSlot ℂ :=
  fun i a => ((realNumerator i a : ℂ) + Complex.I * (imagNumerator i a : ℂ)) /
    (factorScale : ℂ)

def gram : Matrix OccupiedSlot OccupiedSlot ℂ := factor.conjTranspose * factor
def rawGamma : Matrix Basis Basis ℂ := Reentry.Source.targetRealized
def candidateGamma : Matrix Basis Basis ℂ := (2 : ℂ) • (factor * factor.conjTranspose)

theorem raw_gamma_hermitian : rawGamma.IsHermitian :=
  Reentry.Producer.targetRealized_hermitian

theorem raw_gamma_entry (i j : Basis) : rawGamma i j =
    ((Reentry.Source.targetRealNumerator i j : ℂ) +
      Complex.I * (Reentry.Source.targetImagNumerator i j : ℂ)) / (gammaScale : ℂ) := rfl

theorem gram_positive_semidef : gram.PosSemidef := by
  change (factor.conjTranspose * factor).PosSemidef
  exact Matrix.posSemidef_conjTranspose_mul_self factor

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
