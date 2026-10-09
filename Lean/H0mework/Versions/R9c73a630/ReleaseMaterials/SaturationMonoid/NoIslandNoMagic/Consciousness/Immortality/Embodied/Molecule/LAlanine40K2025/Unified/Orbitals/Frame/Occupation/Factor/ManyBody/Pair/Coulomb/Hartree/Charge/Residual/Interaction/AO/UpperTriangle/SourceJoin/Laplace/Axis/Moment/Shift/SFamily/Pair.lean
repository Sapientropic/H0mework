import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.Pair

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.SFamily
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
noncomputable section

theorem s_right_axis_shape (left right : Term) (i : Fin 3) (x : ℝ)
    (hs : Axis.sPowers right) :
    axisShape left right i x =
      Real.exp (-((left.exponent : ℝ) * (right.exponent : ℝ) /
        Axis.sPairRate left right *
        ((left.centre i : ℝ) - (right.centre i : ℝ))^2)) *
      ((x-(left.centre i : ℝ))^left.powers i *
        Real.exp (-(Axis.sPairRate left right) *
          (x-Axis.sPairCentre left right i)^2)) := by
  unfold axisShape Axis.sPairRate Axis.sPairCentre
  rw [hs i]
  simp only [pow_zero, mul_one]
  ring

theorem s_right_pair_shape (left right : Term) (x : Point)
    (hs : Axis.sPowers right) :
    pairShape left right x =
      Axis.sPairCoefficient left right *
        ∏ i : Fin 3,
          (x i-(left.centre i : ℝ))^left.powers i *
            Real.exp (-(Axis.sPairRate left right) *
              (x i-Axis.sPairCentre left right i)^2) := by
  unfold pairShape Axis.sPairCoefficient Axis.sPairAttenuation
  rw [s_right_axis_shape left right 0 (x 0) hs,
    s_right_axis_shape left right 1 (x 1) hs,
    s_right_axis_shape left right 2 (x 2) hs]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.SFamily
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
