import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.HeatP0
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Quartet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.J

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open BasinRefinement.GlobalSource MeasureTheory Set
noncomputable section

theorem primitive_p0_zero (term : Term)
    (hp : sourceP0 term) (positive : 0 < term.exponent) :
    Laplace.primitiveHeatInteraction
      (term,Axis.originalS) (Axis.originalS,Axis.originalS) = 0 := by
  unfold Laplace.primitiveHeatInteraction
  calc
    (∫ t in Ioi (0 : ℝ),
      ∫ z : Point × Point,
        Laplace.heatIntegrand term Axis.originalS Axis.originalS Axis.originalS z t) =
      ∫ t in Ioi (0 : ℝ), (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact p0_heat_inner_zero term t hp positive ht
    _ = 0 := by simp

theorem original_p0_ERI_zero :
    electronRepulsion (3 : Basis) 2 2 2 = 0 := by
  rw [Laplace.electron_repulsion_heat_finite]
  unfold Laplace.pairInteractionHeatFinite
  rw [Axis.original_s_pair_terms]
  simp only [List.map_singleton,List.sum_singleton]
  have hmap :
      ((pairTerms (3 : Basis) 2).map fun pair =>
        Laplace.primitiveHeatInteraction pair (Axis.originalS,Axis.originalS)) =
      (pairTerms (3 : Basis) 2).map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro pair member
    rcases List.mem_flatMap.mp member with ⟨term,termMember,rightMember⟩
    rcases List.mem_map.mp rightMember with ⟨right,rightIn,identified⟩
    rw [Axis.original_s_singleton] at rightIn
    have hright : right = Axis.originalS := List.mem_singleton.mp rightIn
    subst right
    have hpair : pair = (term,Axis.originalS) := identified.symm
    subst pair
    exact primitive_p0_zero term
      (original_p0_source term termMember)
      (source_exponents_positive 3 term termMember)
  rw [hmap]
  simp

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
