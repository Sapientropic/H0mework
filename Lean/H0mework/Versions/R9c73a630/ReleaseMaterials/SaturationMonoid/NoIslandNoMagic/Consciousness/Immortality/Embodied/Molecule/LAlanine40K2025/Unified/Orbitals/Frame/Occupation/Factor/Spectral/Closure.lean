import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Spectral.ProjectorComparison
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Spectral
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
noncomputable section

structure Material where
  parent : Factor.Material
  originalGamma : Matrix Basis Basis ℂ
  occupiedCount : ℕ
  spectralProjector : Matrix Basis Basis ℂ
  sourceProjector : Matrix Basis Basis ℂ
  spectralResidual : Matrix Basis Basis ℂ

def material : Material where
  parent := Factor.material
  originalGamma := Occupation.gamma
  occupiedCount := Occupation.occupiedCount
  spectralProjector := Occupation.projector
  sourceProjector := Factor.projector24
  spectralResidual := Occupation.residual

theorem parent_identity : material.parent = Factor.material := rfl
theorem gamma_identity : material.originalGamma = material.parent.originalGamma := rfl
theorem count_identity : material.occupiedCount = 24 := actual_occupied_count

structure Closure : Prop where
  parent : Factor.Closure
  parentIdentity : type_of% parent_identity
  gammaIdentity : type_of% gamma_identity
  count : material.occupiedCount = 24
  trace : material.spectralProjector.trace = (24 : ℂ)
  residual : ‖material.spectralResidual‖ < (1 / 1000 : ℝ)
  projectorNear : ‖material.spectralProjector - material.sourceProjector‖ <
    (1 / 1000 : ℝ)
  sourceTrace : material.sourceProjector.trace = (24 : ℂ)

theorem sourceGeneratedClosure : Closure :=
  ⟨Factor.sourceGeneratedClosure,parent_identity,gamma_identity,count_identity,
    source_rank_matches_original_threshold.1,actual_spectral_residual_small,
    actual_spectral_projector_near_factor,source_rank_matches_original_threshold.2⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
