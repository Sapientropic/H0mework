import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Primitive
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceCoulomb
open BasinRefinement.ContinuousGradient BasinRefinement.GlobalSource MeasureTheory Set
noncomputable section

attribute [fun_prop] BasinRefinement.SourceCoulomb.distance_continuous

@[fun_prop] theorem pair_shape_continuous (left right : Term) :
    Continuous (pairShape left right) := by
  unfold pairShape axisShape
  fun_prop

theorem heat_continuous (left right nextLeft nextRight : Term) :
    Continuous (fun z : (Point × Point) × ℝ =>
      heatIntegrand left right nextLeft nextRight z.1 z.2) := by
  unfold heatIntegrand primitiveAmplitude
  fun_prop (disch := norm_num)

theorem off_diagonal_ae :
    ∀ᵐ z : Point × Point ∂(volume : Measure (Point × Point)), z.1 ≠ z.2 := by
  rw [ae_iff]
  simpa [Set.diagonal,eq_comm] using product_diagonal_null


end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
