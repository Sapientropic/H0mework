import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ProjectionError
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
attribute [local irreducible] rawGamma projector24 Occupation.gamma

theorem actual_U_gamma_projection_error :
    ‖Occupation.gamma - (2 : ℂ) • projector24‖ < (1 / 10^5 : ℝ) := by
  have transport := Frame.actual_registered_state_error rawGamma
  have transportBound : ‖Occupation.gamma - rawGamma‖ ≤
      (4 / 10^7 : ℝ) * ‖rawGamma‖ := by
    simpa only [Occupation.gamma,rawGamma] using transport
  have sourceBound := source_projection_error_small
  have sizeBound := raw_gamma_norm_lt_three
  have triangle : ‖Occupation.gamma - (2 : ℂ) • projector24‖ ≤
      ‖Occupation.gamma - rawGamma‖ +
        ‖rawGamma - (2 : ℂ) • projector24‖ := by
    convert norm_add_le (Occupation.gamma - rawGamma)
      (rawGamma - (2 : ℂ) • projector24) using 1
    abel
  nlinarith

def coefficient24 (a : OccupiedSlot) : Basis → ℂ :=
  normalizedFactor *ᵥ Pi.single a (1 : ℂ)

def wave24 (a : OccupiedSlot) (time : ℝ) (x : Point) : Hilbert :=
  sourceWave (coefficient24 a) time x

theorem wave24_orthonormal (a b : OccupiedSlot) (time : ℝ) :
    (∫ x : Point, inner ℂ (wave24 a time x) (wave24 b time x)) =
      if a = b then 1 else 0 := by
  change (∫ x : Point,
    inner ℂ (sourceWave (coefficient24 a) time x)
      (sourceWave (coefficient24 b) time x)) = _
  unfold coefficient24
  rw [wave_pair_integral actual_gram_positive]
  rw [Matrix.star_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul]
  change star (Pi.single a (1 : ℂ)) ᵥ*
    (normalizedFactor.conjTranspose * normalizedFactor) ⬝ᵥ Pi.single b (1 : ℂ) = _
  rw [normalized_isometry,Matrix.vecMul_one]
  classical
  simp [dotProduct,Pi.star_apply,Pi.single_apply,eq_comm]

theorem actual_U_gamma_response (a b : OccupiedSlot) (time : ℝ) :
    (∫ x : Point, inner ℂ (wave24 a time x)
      (sourceWave (Occupation.gamma *ᵥ coefficient24 b) time x)) =
        star (coefficient24 a) ⬝ᵥ (Occupation.gamma *ᵥ coefficient24 b) := by
  exact source_matrix_response actual_gram_positive _ _ _ _

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
