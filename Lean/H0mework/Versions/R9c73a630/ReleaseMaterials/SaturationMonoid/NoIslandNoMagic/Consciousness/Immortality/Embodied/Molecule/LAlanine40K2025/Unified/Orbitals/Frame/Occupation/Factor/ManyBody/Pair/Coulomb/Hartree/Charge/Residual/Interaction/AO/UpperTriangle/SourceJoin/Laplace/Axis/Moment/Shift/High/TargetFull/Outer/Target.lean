import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer.Quartet

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def targetCompactJ (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      sourceCompactQuartet
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) i j

theorem target_compact_J (i j : Basis) :
    SourceJoin.material.targetJ i j = targetCompactJ i j := by
  rw [TargetFull.target_full_J]
  unfold TargetFull.targetFullJ targetCompactJ
  apply Finset.sum_congr rfl
  intro address _
  rw [← source_compact_quartet, ← TargetFull.source_full_quartet]

theorem parent_same_source (i j : Basis) :
    TargetFull.targetFullJ i j = targetCompactJ i j := by
  rw [← TargetFull.target_full_J i j, target_compact_J i j]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
