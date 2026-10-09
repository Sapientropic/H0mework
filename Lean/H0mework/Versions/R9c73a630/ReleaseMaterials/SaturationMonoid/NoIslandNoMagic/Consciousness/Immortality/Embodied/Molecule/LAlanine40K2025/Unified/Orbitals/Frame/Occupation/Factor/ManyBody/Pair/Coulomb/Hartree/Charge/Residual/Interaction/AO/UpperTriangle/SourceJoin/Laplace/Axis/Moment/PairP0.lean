import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.SourceP0
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.GenericS

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
noncomputable section

theorem p0_axis_shape (term : Term) (axis : Fin 3) (x : ℝ)
    (hp : sourceP0 term) (positive : 0 < term.exponent) :
    axisShape term Axis.originalS axis x =
      (x-Axis.originalCentre axis)^term.powers axis *
        Real.exp (-(Axis.sPairRate term Axis.originalS) *
          (x-Axis.originalCentre axis)^2) := by
  have hcentre : term.centre axis = Axis.originalS.centre axis := hp.2.2.2 axis
  have hsum : (term.exponent : ℝ) + (Axis.originalS.exponent : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact add_pos (by exact_mod_cast positive)
      (by exact_mod_cast Axis.original_s_exponent)
  have hcomb : centre (term.exponent : ℝ) (Axis.originalS.exponent : ℝ)
      (term.centre axis : ℝ) (Axis.originalS.centre axis : ℝ) =
      (Axis.originalS.centre axis : ℝ) := by
    rw [hcentre]
    unfold centre
    field_simp [hsum]
  unfold axisShape Axis.sPairRate Axis.originalCentre
  rw [Axis.original_s_powers axis,hcomb,hcentre]
  simp

theorem p0_pair_shape (term : Term) (x : Point)
    (hp : sourceP0 term) (positive : 0 < term.exponent) :
    pairShape term Axis.originalS x =
      (term.weight : ℝ) * Axis.originalWeight *
        (x 0-Axis.originalCentre 0) *
          ∏ axis : Fin 3,
            Real.exp (-(Axis.sPairRate term Axis.originalS) *
              (x axis-Axis.originalCentre axis)^2) := by
  unfold pairShape
  rw [p0_axis_shape term 0 (x 0) hp positive,
    p0_axis_shape term 1 (x 1) hp positive,
    p0_axis_shape term 2 (x 2) hp positive]
  rw [hp.1,hp.2.1,hp.2.2.1]
  simp only [pow_one,pow_zero,one_mul,Fin.prod_univ_succ,
    Fin.prod_univ_zero,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  unfold Axis.originalWeight
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
