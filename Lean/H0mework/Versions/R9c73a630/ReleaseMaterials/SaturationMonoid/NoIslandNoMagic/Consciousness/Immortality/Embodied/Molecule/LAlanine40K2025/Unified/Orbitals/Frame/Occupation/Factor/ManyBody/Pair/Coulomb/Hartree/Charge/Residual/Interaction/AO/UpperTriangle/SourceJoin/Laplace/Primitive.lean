import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Kernel
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Finite

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceCoulomb
open BasinRefinement.ContinuousGradient BasinRefinement.GlobalSource MeasureTheory Set
noncomputable section

def primitiveAmplitude (left right nextLeft nextRight : Term)
    (z : Point × Point) : ℝ :=
  pairShape left right z.1 * pairShape nextLeft nextRight z.2

def heatIntegrand (left right nextLeft nextRight : Term)
    (z : Point × Point) (t : ℝ) : ℝ :=
  primitiveAmplitude left right nextLeft nextRight z *
    (2 / Real.sqrt Real.pi) *
      Real.exp (-(distance (z.2-z.1))^2 * t^2)

theorem primitive_kernel_heat (left right nextLeft nextRight : Term)
    (z : Point × Point) :
    pairShape left right z.1 * pairShape nextLeft nextRight z.2 *
      kernel (z.2-z.1) =
        ∫ t in Ioi (0 : ℝ), heatIntegrand left right nextLeft nextRight z t := by
  rw [kernel_laplace]
  simp only [heatIntegrand, primitiveAmplitude, integral_const_mul]
  ring

theorem primitive_interaction_heat (left right nextLeft nextRight : Term) :
    GaussianPair.primitiveInteraction (left,right) (nextLeft,nextRight) =
      ∫ z : Point × Point,
        ∫ t in Ioi (0 : ℝ),
          heatIntegrand left right nextLeft nextRight z t := by
  unfold GaussianPair.primitiveInteraction
  congr 1
  funext z
  exact primitive_kernel_heat left right nextLeft nextRight z

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
