import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Normalize

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def projector24 : Matrix Basis Basis ℂ := normalizedFactor * normalizedFactor.conjTranspose

theorem projector24_positive : projector24.PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose normalizedFactor

theorem projector24_idempotent : projector24 * projector24 = projector24 := by
  unfold projector24
  calc
    _ = normalizedFactor * (normalizedFactor.conjTranspose * normalizedFactor) *
        normalizedFactor.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [normalized_isometry,Matrix.mul_one]

theorem projector24_trace : projector24.trace = (24 : ℂ) := by
  rw [projector24,Matrix.trace_mul_comm,normalized_isometry]
  simp [Matrix.trace_one,Fintype.card_fin]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
