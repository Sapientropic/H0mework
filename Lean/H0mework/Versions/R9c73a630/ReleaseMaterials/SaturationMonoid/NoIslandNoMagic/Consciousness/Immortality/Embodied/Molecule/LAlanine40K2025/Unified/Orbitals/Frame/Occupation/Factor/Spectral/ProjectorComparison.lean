import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Spectral.Count

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Spectral
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
noncomputable section
attribute [local irreducible] Occupation.gamma Occupation.projector Factor.projector24

theorem actual_spectral_projector_near_factor :
    ‖Occupation.projector - projector24‖ < (1 / 1000 : ℝ) := by
  have identity : (2 : ℂ) • (Occupation.projector - projector24) =
      (Occupation.gamma - (2 : ℂ) • projector24) - Occupation.residual := by
    rw [Occupation.gamma_projector_residual]
    module
  have triangle := norm_sub_le (Occupation.gamma - (2 : ℂ) • projector24)
    Occupation.residual
  rw [← identity,norm_smul] at triangle
  have two : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [two] at triangle
  have source := actual_U_gamma_projection_error
  have spectral := actual_spectral_residual_small
  nlinarith

theorem source_rank_matches_original_threshold :
    Occupation.projector.trace = (24 : ℂ) ∧ projector24.trace = (24 : ℂ) := by
  exact ⟨by rw [Occupation.projector_trace,actual_occupied_count]; norm_num,
    projector24_trace⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
