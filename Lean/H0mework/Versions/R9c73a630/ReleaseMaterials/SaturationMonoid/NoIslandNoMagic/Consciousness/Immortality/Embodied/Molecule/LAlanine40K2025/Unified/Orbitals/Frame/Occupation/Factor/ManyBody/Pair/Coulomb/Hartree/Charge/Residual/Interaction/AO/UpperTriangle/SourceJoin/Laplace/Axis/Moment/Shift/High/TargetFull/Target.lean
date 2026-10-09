import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Quartet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear.Target

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def targetFullJ (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      sourceFullQuartet
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) i j

theorem target_full_J (i j : Basis) :
    SourceJoin.material.targetJ i j = targetFullJ i j := by
  rw [Laplace.target_heat_J_exact]
  unfold Laplace.targetHeatJ targetFullJ
  apply Finset.sum_congr rfl
  intro address _
  rw [← Laplace.electron_repulsion_heat_finite,
    source_full_quartet]

theorem prior_linear_same_source (i j : Basis) :
    TargetLinear.targetLinearJ i j = targetFullJ i j := by
  rw [← TargetLinear.target_linear_J i j, target_full_J i j]

def allTargetEntries : Finset (Basis × Basis) := Finset.univ

theorem all_target_entries_card : allTargetEntries.card = 9604 := by
  simp [allTargetEntries]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
