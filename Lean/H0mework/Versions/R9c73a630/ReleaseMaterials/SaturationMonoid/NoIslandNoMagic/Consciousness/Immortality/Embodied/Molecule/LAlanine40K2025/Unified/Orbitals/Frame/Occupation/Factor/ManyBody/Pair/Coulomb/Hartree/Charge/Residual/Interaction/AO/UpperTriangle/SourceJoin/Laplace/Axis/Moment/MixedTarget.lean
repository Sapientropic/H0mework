import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.MixedQuartet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.TargetP0

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

theorem original_p0_s_cross_census :
    (pairTerms (3 : Basis) 2).length = 3 ∧
    (pairTerms (14 : Basis) 14).length = 36 := by
  constructor <;> decide +kernel

def targetHeatJ1414Rest : ℝ :=
  ∑ address ∈ (Finset.univ : Finset (Fin 4851)).erase 196,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      Laplace.pairInteractionHeatFinite
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) 14 14

theorem target_heat_J1414_mixed_component :
    Laplace.targetHeatJ 14 14 =
      (SourceJoin.sourceCoefficientAt (196 : Fin 4851) : ℝ) *
        originalP0SCrossQuartet + targetHeatJ1414Rest := by
  unfold Laplace.targetHeatJ targetHeatJ1414Rest
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin 4851))
    (fun address => (SourceJoin.sourceCoefficientAt address : ℝ) *
      Laplace.pairInteractionHeatFinite
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) 14 14)
    (Finset.mem_univ (196 : Fin 4851))]
  have hleft : SourceJoin.targetLeft (196 : Fin 4851).val = (2 : Basis) := by
    simpa using original_p0_target_address.1
  have hright : SourceJoin.targetRight (196 : Fin 4851).val = (3 : Basis) := by
    simpa using original_p0_target_address.2
  rw [hleft,hright]
  rw [← Laplace.electron_repulsion_heat_finite,
    electronRepulsion_first_swap,
    original_p0_s_cross_quartet]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
