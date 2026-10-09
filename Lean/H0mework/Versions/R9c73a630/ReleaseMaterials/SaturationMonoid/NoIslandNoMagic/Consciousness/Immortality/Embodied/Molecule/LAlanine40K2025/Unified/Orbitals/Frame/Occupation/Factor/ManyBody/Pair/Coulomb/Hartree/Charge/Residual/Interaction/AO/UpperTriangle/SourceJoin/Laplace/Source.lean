import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Exchange

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceFiniteData BasinRefinement.SourceGaussianModel
open BasinRefinement.SourceCoulomb BasinRefinement.ContinuousGradient MeasureTheory Set
noncomputable section

def primitiveHeatInteraction (left right : Term × Term) : ℝ :=
  ∫ t in Ioi (0 : ℝ),
    ∫ z : Point × Point,
      heatIntegrand left.1 left.2 right.1 right.2 z t

def pairInteractionHeatFinite (i j k l : Basis) : ℝ :=
  ((pairTerms i j).map fun left =>
    ((pairTerms k l).map fun right => primitiveHeatInteraction left right).sum).sum

theorem source_primitive_heat
    (i j k l : Basis) (left right : Term × Term)
    (leftMember : left ∈ pairTerms i j)
    (rightMember : right ∈ pairTerms k l) :
    primitiveInteraction left right = primitiveHeatInteraction left right := by
  have hp := pair_terms_positive i j left leftMember
  have hq := pair_terms_positive k l right rightMember
  exact primitive_interaction_heat_swapped
    left.1 left.2 right.1 right.2 hp.1 hp.2 hq.1 hq.2

theorem pair_interaction_heat_finite (i j k l : Basis) :
    pairInteractionFinite i j k l = pairInteractionHeatFinite i j k l := by
  unfold pairInteractionFinite pairInteractionHeatFinite
  apply congrArg List.sum
  apply List.map_congr_left
  intro left leftMember
  apply congrArg List.sum
  apply List.map_congr_left
  intro right rightMember
  exact source_primitive_heat i j k l left right leftMember rightMember

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
