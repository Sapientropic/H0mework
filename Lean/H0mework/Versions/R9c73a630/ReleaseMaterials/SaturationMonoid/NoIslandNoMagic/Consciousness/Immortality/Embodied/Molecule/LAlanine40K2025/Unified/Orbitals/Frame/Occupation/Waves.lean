import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation
open BasinRefinement SourceFiniteData SourceGaussianModel MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped Matrix BigOperators
noncomputable section

def naturalCoefficient (i : Basis) : Basis → ℂ :=
  (gamma_hermitian.eigenvectorUnitary : Matrix Basis Basis ℂ) *ᵥ Pi.single i (1 : ℂ)

def naturalWave (i : Basis) (time : ℝ) (x : Point) : Hilbert :=
  sourceWave (naturalCoefficient i) time x

theorem natural_coefficient_eigen (i : Basis) :
    gamma *ᵥ naturalCoefficient i =
      gamma_hermitian.eigenvalues i • naturalCoefficient i := by
  rw [naturalCoefficient,gamma_hermitian.eigenvectorUnitary_mulVec]
  exact gamma_hermitian.mulVec_eigenvectorBasis i

theorem natural_wave_orthonormal (i j : Basis) (time : ℝ) :
    (∫ x : Point, inner ℂ (naturalWave i time x) (naturalWave j time x)) =
      if i=j then 1 else 0 := by
  change (∫ x : Point,
    inner ℂ (sourceWave (naturalCoefficient i) time x)
      (sourceWave (naturalCoefficient j) time x)) = _
  unfold naturalCoefficient
  rw [source_unitary_preserves actual_gram_positive]
  classical
  simp [dotProduct,Pi.star_apply,Pi.single_apply,eq_comm]

theorem natural_gamma_response (i j : Basis) (time : ℝ) :
    (∫ x : Point, inner ℂ (naturalWave i time x)
      (sourceWave (gamma *ᵥ naturalCoefficient j) time x)) =
      gamma_hermitian.eigenvalues j • (if i=j then (1 : ℂ) else 0) := by
  change (∫ x : Point, inner ℂ (sourceWave (naturalCoefficient i) time x)
    (sourceWave (gamma *ᵥ naturalCoefficient j) time x)) = _
  rw [source_matrix_response actual_gram_positive]
  rw [natural_coefficient_eigen]
  rw [dotProduct_smul]
  congr 1
  rw [← wave_pair_integral actual_gram_positive]
  exact natural_wave_orthonormal i j time

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
