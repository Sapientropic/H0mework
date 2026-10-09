import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

theorem electron_repulsion_heat_finite (i j k l : Basis) :
    electronRepulsion i j k l = pairInteractionHeatFinite i j k l :=
  (GaussianPair.pair_interaction_source i j k l).symm.trans
    ((GaussianPair.pair_interaction_finite i j k l).trans
      (pair_interaction_heat_finite i j k l))

def targetHeatJ (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      pairInteractionHeatFinite
        (SourceJoin.targetLeft address.val) (SourceJoin.targetRight address.val) i j

theorem target_heat_J_exact (i j : Basis) :
    SourceJoin.material.targetJ i j = targetHeatJ i j := by
  change SourceJoin.targetAddressedJ i j = targetHeatJ i j
  unfold SourceJoin.targetAddressedJ targetHeatJ
  apply Finset.sum_congr rfl
  intro address _
  rw [electron_repulsion_heat_finite]

theorem original_J_heat_finite (i j : Basis) :
    Interaction.AO.sourceJ i j =
      ∑ k : Basis, ∑ l : Basis,
        Proxy.Correction.d3AO k l * pairInteractionHeatFinite k l i j := by
  rw [GaussianPair.sourceJ_primitive_finite]
  simp only [pair_interaction_heat_finite]

theorem original_hartree_heat_finite :
    Interaction.d3HartreeEnergy = (1 / 2 : ℝ) *
      ∑ i : Basis, ∑ j : Basis,
        Proxy.Correction.d3AO i j *
          (∑ k : Basis, ∑ l : Basis,
            Proxy.Correction.d3AO k l * pairInteractionHeatFinite k l i j) := by
  rw [GaussianPair.original_hartree_primitive_finite]
  simp only [pair_interaction_heat_finite]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
