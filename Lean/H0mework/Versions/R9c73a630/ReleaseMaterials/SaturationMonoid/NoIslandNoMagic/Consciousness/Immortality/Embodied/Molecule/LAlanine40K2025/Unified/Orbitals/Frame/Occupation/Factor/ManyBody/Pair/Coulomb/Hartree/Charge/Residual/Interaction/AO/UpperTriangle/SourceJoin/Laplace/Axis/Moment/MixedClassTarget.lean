import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.MixedClass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.MixedTarget

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def targetP0SRest (i j : Basis) : ℝ :=
  ∑ address ∈ (Finset.univ : Finset (Fin 4851)).erase 196,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      Laplace.pairInteractionHeatFinite
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) i j

theorem target_p0_s_J (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    SourceJoin.material.targetJ i j =
      (SourceJoin.sourceCoefficientAt (196 : Fin 4851) : ℝ) *
        sourceP0SQuartet i j + targetP0SRest i j := by
  rw [Laplace.target_heat_J_exact]
  unfold Laplace.targetHeatJ targetP0SRest
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin 4851))
    (fun address => (SourceJoin.sourceCoefficientAt address : ℝ) *
      Laplace.pairInteractionHeatFinite
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) i j)
    (Finset.mem_univ (196 : Fin 4851))]
  have hleft : SourceJoin.targetLeft (196 : Fin 4851).val = (2 : Basis) := by
    simpa using original_p0_target_address.1
  have hright : SourceJoin.targetRight (196 : Fin 4851).val = (3 : Basis) := by
    simpa using original_p0_target_address.2
  rw [hleft,hright]
  rw [← Laplace.electron_repulsion_heat_finite,
    electronRepulsion_first_swap,
    source_p0_s_bases_quartet i j hi hj]

theorem old_cross_target_is_class_instance :
    targetHeatJ1414Rest = targetP0SRest 14 14 := rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
