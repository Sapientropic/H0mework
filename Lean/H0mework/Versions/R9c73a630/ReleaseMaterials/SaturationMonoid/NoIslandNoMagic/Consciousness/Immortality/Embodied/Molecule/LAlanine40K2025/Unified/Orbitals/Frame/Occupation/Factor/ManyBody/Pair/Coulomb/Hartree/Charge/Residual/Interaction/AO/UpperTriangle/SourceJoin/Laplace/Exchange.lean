import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Integrability

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceCoulomb
open BasinRefinement.ContinuousGradient BasinRefinement.GlobalSource MeasureTheory Set
noncomputable section

theorem primitive_interaction_heat_swapped
    (left right nextLeft nextRight : Term)
    (leftPositive : 0 < left.exponent) (rightPositive : 0 < right.exponent)
    (nextLeftPositive : 0 < nextLeft.exponent)
    (nextRightPositive : 0 < nextRight.exponent) :
    GaussianPair.primitiveInteraction (left,right) (nextLeft,nextRight) =
      ∫ t in Ioi (0 : ℝ),
        ∫ z : Point × Point,
          heatIntegrand left right nextLeft nextRight z t := by
  rw [primitive_interaction_heat]
  exact integral_integral_swap
    (primitive_heat_integrable left right nextLeft nextRight
      leftPositive rightPositive nextLeftPositive nextRightPositive)

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
