import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Waves

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation
open BasinRefinement SourceFiniteData SourceGaussianModel MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped Matrix BigOperators
noncomputable section

theorem natural_projector_eigen (j : Basis) :
    projector *ᵥ naturalCoefficient j = mask j • naturalCoefficient j := by
  let U : Matrix Basis Basis ℂ := gamma_hermitian.eigenvectorUnitary
  have unit : star U * U = 1 := (Unitary.mem_iff.mp gamma_hermitian.eigenvectorUnitary.property).1
  change (U * diagonal * star U) *ᵥ (U *ᵥ Pi.single j (1 : ℂ)) =
    mask j • (U *ᵥ Pi.single j (1 : ℂ))
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc (U * diagonal) (star U) U,unit,Matrix.mul_one]
  rw [← Matrix.mulVec_mulVec,diagonal,Matrix.diagonal_mulVec_single]
  simp

theorem natural_projector_response (i j : Basis) (time : ℝ) :
    (∫ x : Point, inner ℂ (naturalWave i time x)
      (sourceWave (projector *ᵥ naturalCoefficient j) time x)) =
      mask j * (if i=j then (1 : ℂ) else 0) := by
  change (∫ x : Point, inner ℂ (sourceWave (naturalCoefficient i) time x)
    (sourceWave (projector *ᵥ naturalCoefficient j) time x)) = _
  rw [source_matrix_response actual_gram_positive,natural_projector_eigen,dotProduct_smul]
  congr 1
  rw [← wave_pair_integral actual_gram_positive]
  exact natural_wave_orthonormal i j time

theorem natural_residual_response (i j : Basis) (time : ℝ) :
    (∫ x : Point, inner ℂ (naturalWave i time x)
      (sourceWave (residual *ᵥ naturalCoefficient j) time x)) =
      gamma_hermitian.eigenvalues j • (if i=j then (1 : ℂ) else 0) -
        (2 : ℂ) * mask j * (if i=j then (1 : ℂ) else 0) := by
  change (∫ x : Point, inner ℂ (sourceWave (naturalCoefficient i) time x)
    (sourceWave (residual *ᵥ naturalCoefficient j) time x)) = _
  rw [source_matrix_response actual_gram_positive]
  have linear :
      star (naturalCoefficient i) ⬝ᵥ (residual *ᵥ naturalCoefficient j) =
        star (naturalCoefficient i) ⬝ᵥ (gamma *ᵥ naturalCoefficient j) -
          (2 : ℂ) * (star (naturalCoefficient i) ⬝ᵥ (projector *ᵥ naturalCoefficient j)) := by
    simp [residual,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul]
  rw [linear]
  have gammaRead := natural_gamma_response i j time
  have projectorRead := natural_projector_response i j time
  change (∫ x : Point, inner ℂ (sourceWave (naturalCoefficient i) time x)
    (sourceWave (gamma *ᵥ naturalCoefficient j) time x)) = _ at gammaRead
  change (∫ x : Point, inner ℂ (sourceWave (naturalCoefficient i) time x)
    (sourceWave (projector *ᵥ naturalCoefficient j) time x)) = _ at projectorRead
  rw [source_matrix_response actual_gram_positive] at gammaRead projectorRead
  rw [gammaRead,projectorRead]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
