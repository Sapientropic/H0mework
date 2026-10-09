import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.GenericS

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
noncomputable section

theorem shifted_axis_shape (term : Term) (i : Fin 3) (x : ℝ) :
    axisShape term Axis.originalS i x =
      Real.exp (-((term.exponent : ℝ) * Axis.originalAlpha /
        Axis.sPairRate term Axis.originalS *
        ((term.centre i : ℝ) - Axis.originalCentre i)^2)) *
      ((x-(term.centre i : ℝ))^term.powers i *
        Real.exp (-(Axis.sPairRate term Axis.originalS) *
          (x-Axis.sPairCentre term Axis.originalS i)^2)) := by
  unfold axisShape Axis.sPairRate Axis.sPairCentre Axis.originalAlpha Axis.originalCentre
  rw [Axis.original_s_powers i]
  simp only [pow_zero, mul_one]
  ring

theorem shifted_pair_shape (term : Term) (x : Point) :
    pairShape term Axis.originalS x =
      Axis.sPairCoefficient term Axis.originalS *
        ∏ i : Fin 3,
          (x i-(term.centre i : ℝ))^term.powers i *
            Real.exp (-(Axis.sPairRate term Axis.originalS) *
              (x i-Axis.sPairCentre term Axis.originalS i)^2) := by
  unfold pairShape Axis.sPairCoefficient Axis.sPairAttenuation
  rw [shifted_axis_shape term 0 (x 0),
    shifted_axis_shape term 1 (x 1),
    shifted_axis_shape term 2 (x 2)]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  unfold Axis.originalAlpha Axis.originalCentre
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
