import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis.Quartet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.MixedClassTarget

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def pAddress (axis : Fin 3) : Fin 4851 := ⟨196+axis.val, by omega⟩

theorem p_axis_target_address :
    ∀ axis : Fin 3,
      SourceJoin.targetLeft (pAddress axis).val = (2 : Basis) ∧
      SourceJoin.targetRight (pAddress axis).val = pBasis axis := by
  decide +kernel

def targetPAxisRest (axis : Fin 3) (i j : Basis) : ℝ :=
  ∑ address ∈ (Finset.univ : Finset (Fin 4851)).erase (pAddress axis),
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      Laplace.pairInteractionHeatFinite
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) i j

theorem target_p_axis_s_J (axis : Fin 3) (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    SourceJoin.material.targetJ i j =
      (SourceJoin.sourceCoefficientAt (pAddress axis) : ℝ) *
        sourcePAxisSQuartet axis i j + targetPAxisRest axis i j := by
  rw [Laplace.target_heat_J_exact]
  unfold Laplace.targetHeatJ targetPAxisRest
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin 4851))
    (fun address => (SourceJoin.sourceCoefficientAt address : ℝ) *
      Laplace.pairInteractionHeatFinite
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) i j)
    (Finset.mem_univ (pAddress axis))]
  rw [(p_axis_target_address axis).1,(p_axis_target_address axis).2]
  rw [← Laplace.electron_repulsion_heat_finite,
    electronRepulsion_first_swap,
    source_p_axis_s_bases_quartet axis i j hi hj]

theorem old_p0_address_is_axis_zero : pAddress 0 = (196 : Fin 4851) := rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
