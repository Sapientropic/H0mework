import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.QuartetP0
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Target

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

theorem original_p0_target_address :
    SourceJoin.targetLeft 196 = (2 : Basis) ∧
    SourceJoin.targetRight 196 = (3 : Basis) := by decide +kernel

theorem original_p0_target_term_zero :
    (SourceJoin.sourceCoefficientAt (196 : Fin 4851) : ℝ) *
      Laplace.pairInteractionHeatFinite
        (SourceJoin.targetLeft (196 : Fin 4851).val)
        (SourceJoin.targetRight (196 : Fin 4851).val) 2 2 = 0 := by
  have hleft : SourceJoin.targetLeft (196 : Fin 4851).val = (2 : Basis) := by
    simpa using original_p0_target_address.1
  have hright : SourceJoin.targetRight (196 : Fin 4851).val = (3 : Basis) := by
    simpa using original_p0_target_address.2
  rw [hleft,hright]
  rw [← Laplace.electron_repulsion_heat_finite]
  rw [electronRepulsion_first_swap]
  rw [original_p0_ERI_zero]
  ring

def targetHeatJ22WithoutP0 : ℝ :=
  ∑ address ∈ (Finset.univ : Finset (Fin 4851)).erase 196,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      Laplace.pairInteractionHeatFinite
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) 2 2

theorem target_heat_J22_p0_erase :
    Laplace.targetHeatJ 2 2 = targetHeatJ22WithoutP0 := by
  unfold Laplace.targetHeatJ targetHeatJ22WithoutP0
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin 4851))
    (fun address => (SourceJoin.sourceCoefficientAt address : ℝ) *
      Laplace.pairInteractionHeatFinite
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) 2 2)
    (Finset.mem_univ (196 : Fin 4851))]
  rw [original_p0_target_term_zero]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
