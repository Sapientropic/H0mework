import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceHeat
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.J

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open BasinRefinement.SourceFiniteData BasinRefinement.SourceGaussianModel
open BasinRefinement.GlobalSource
open BasinRefinement.SourceCoulomb
open MeasureTheory
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open scoped BigOperators
noncomputable section

theorem original_s_pair_terms :
    pairTerms (2 : Basis) (2 : Basis) = [(originalS,originalS)] := by
  simp [pairTerms,original_s_singleton]

theorem original_s_ERI_heat :
    electronRepulsion (2 : Basis) 2 2 2 =
      ∫ t in Set.Ioi (0 : ℝ),
        ∫ z : Point × Point,
          heatIntegrand originalS originalS originalS originalS z t := by
  rw [electron_repulsion_heat_finite]
  simp [pairInteractionHeatFinite,original_s_pair_terms,primitiveHeatInteraction]

theorem original_s_ERI_outer_closed :
    electronRepulsion (2 : Basis) 2 2 2 =
      ∫ t in Set.Ioi (0 : ℝ),
        originalWeight^4 * (2 / Real.sqrt Real.pi) *
          (Real.pi / Real.sqrt
            ((2*originalAlpha)*(2*originalAlpha) +
              ((2*originalAlpha)+(2*originalAlpha))*t^2))^3 := by
  rw [original_s_ERI_heat]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact original_s_heat_inner_simple t ht

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
