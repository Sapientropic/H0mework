import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Quartet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData MeasureTheory Set
open scoped BigOperators
noncomputable section

theorem target_s_address :
    SourceJoin.targetLeft 195 = (2 : Basis) ∧
    SourceJoin.targetRight 195 = (2 : Basis) := by decide +kernel

theorem heat_quartet_2222_outer :
    Laplace.material.heatQuartet 2 2 2 2 =
      ∫ t in Ioi (0 : ℝ),
        originalWeight^4 * (2 / Real.sqrt Real.pi) *
          (Real.pi / Real.sqrt
            ((2*originalAlpha)*(2*originalAlpha) +
              ((2*originalAlpha)+(2*originalAlpha))*t^2))^3 :=
  (Laplace.quartet_exact 2 2 2 2).trans original_s_ERI_outer_closed

def targetHeatJ22Rest : ℝ :=
  ∑ address ∈ (Finset.univ : Finset (Fin 4851)).erase 195,
    (SourceJoin.sourceCoefficientAt address : ℝ) *
      Laplace.pairInteractionHeatFinite
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) 2 2

theorem target_heat_J22_decomposition :
    Laplace.material.heatTargetJ 2 2 =
      (SourceJoin.sourceCoefficientAt 195 : ℝ) *
        (∫ t in Ioi (0 : ℝ),
          originalWeight^4 * (2 / Real.sqrt Real.pi) *
            (Real.pi / Real.sqrt
              ((2*originalAlpha)*(2*originalAlpha) +
                ((2*originalAlpha)+(2*originalAlpha))*t^2))^3) +
        targetHeatJ22Rest := by
  change Laplace.targetHeatJ 2 2 = _
  unfold Laplace.targetHeatJ targetHeatJ22Rest
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin 4851))
    (fun address => (SourceJoin.sourceCoefficientAt address : ℝ) *
      Laplace.pairInteractionHeatFinite
        (SourceJoin.targetLeft address.val)
        (SourceJoin.targetRight address.val) 2 2)
    (Finset.mem_univ (195 : Fin 4851))]
  have hleft : SourceJoin.targetLeft (195 : Fin 4851).val = (2 : Basis) := by
    simpa using target_s_address.1
  have hright : SourceJoin.targetRight (195 : Fin 4851).val = (2 : Basis) := by
    simpa using target_s_address.2
  rw [hleft,hright]
  rw [← heat_quartet_2222_outer]
  rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
