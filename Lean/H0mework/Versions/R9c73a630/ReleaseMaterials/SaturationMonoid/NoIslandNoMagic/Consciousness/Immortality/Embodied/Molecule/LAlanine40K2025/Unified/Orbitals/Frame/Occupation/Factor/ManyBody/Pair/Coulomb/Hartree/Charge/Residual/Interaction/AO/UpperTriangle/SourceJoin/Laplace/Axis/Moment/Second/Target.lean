import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second.Quartet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis.TargetAll

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def dAddress : Fin 4851 := 204

theorem original_d_address :
    SourceJoin.targetLeft dAddress.val = (2 : Basis) ∧
    SourceJoin.targetRight dAddress.val = (11 : Basis) := by decide +kernel

theorem d_address_not_p : AnyAxis.pAxisAtAddress dAddress = none := by decide +kernel

theorem heat_at_d_address (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    Laplace.pairInteractionHeatFinite
      (SourceJoin.targetLeft dAddress.val)
      (SourceJoin.targetRight dAddress.val) i j =
        sourceDSQuartet i j := by
  rw [original_d_address.1,original_d_address.2]
  rw [← Laplace.electron_repulsion_heat_finite,
    electronRepulsion_first_swap,
    source_d_s_bases_quartet i j hi hj]

def targetP3DHeatJ (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      if address = dAddress then sourceDSQuartet i j
      else match AnyAxis.pAxisAtAddress address with
        | some axis => AnyAxis.sourcePAxisSQuartet axis i j
        | none => Laplace.pairInteractionHeatFinite
            (SourceJoin.targetLeft address.val)
            (SourceJoin.targetRight address.val) i j

theorem target_p3d_J (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    SourceJoin.material.targetJ i j = targetP3DHeatJ i j := by
  rw [AnyAxis.target_three_p_J i j hi hj]
  unfold AnyAxis.targetThreePHeatJ targetP3DHeatJ
  apply Finset.sum_congr rfl
  intro address _
  by_cases h : address = dAddress
  · subst address
    simp only [d_address_not_p]
    rw [heat_at_d_address i j hi hj]
    simp
  · simp only [if_neg h]
    rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
