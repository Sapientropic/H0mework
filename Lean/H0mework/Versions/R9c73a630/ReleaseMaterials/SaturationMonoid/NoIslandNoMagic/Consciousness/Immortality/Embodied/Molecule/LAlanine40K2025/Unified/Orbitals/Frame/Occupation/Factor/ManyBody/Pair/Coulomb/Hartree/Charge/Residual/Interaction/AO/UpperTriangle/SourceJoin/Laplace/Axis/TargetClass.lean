import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceClass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def sourceSTargetAddresses : Finset (Fin 4851) :=
  Finset.univ.filter (fun address =>
    SourceJoin.targetLeft address.val ∈ sourceSBases ∧
      SourceJoin.targetRight address.val ∈ sourceSBases)

theorem source_s_target_address_count : sourceSTargetAddresses.card = 528 := by
  decide +kernel

def targetSHeatJ (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    if address ∈ sourceSTargetAddresses then
      (SourceJoin.sourceCoefficientAt address : ℝ) *
        sourceSQuartet (SourceJoin.targetLeft address.val)
          (SourceJoin.targetRight address.val) i j
    else
      (SourceJoin.sourceCoefficientAt address : ℝ) *
        Laplace.pairInteractionHeatFinite
          (SourceJoin.targetLeft address.val)
          (SourceJoin.targetRight address.val) i j

theorem target_s_heat_J_exact (i j : Basis)
    (hi : i ∈ sourceSBases) (hj : j ∈ sourceSBases) :
    SourceJoin.material.targetJ i j = targetSHeatJ i j := by
  rw [Laplace.target_heat_J_exact]
  unfold Laplace.targetHeatJ targetSHeatJ
  apply Finset.sum_congr rfl
  intro address _
  by_cases hs : address ∈ sourceSTargetAddresses
  · rw [if_pos hs]
    have hsource := (Finset.mem_filter.mp hs).2
    have quartet := source_s_bases_quartet
      (SourceJoin.targetLeft address.val)
      (SourceJoin.targetRight address.val) i j
      hsource.1 hsource.2 hi hj
    rw [← Laplace.electron_repulsion_heat_finite,quartet]
  · rw [if_neg hs]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
