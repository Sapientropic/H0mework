import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.GenericS

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
noncomputable section

theorem low_axis_shape (term : Term) (i : Fin 3) (x : ℝ)
    (hl : sourceLow term) (positive : 0 < term.exponent) :
    axisShape term Axis.originalS i x =
      (x-Axis.originalCentre i)^term.powers i *
        Real.exp (-(Axis.sPairRate term Axis.originalS) *
          (x-Axis.originalCentre i)^2) := by
  have hcentre : term.centre i = Axis.originalS.centre i := (hl i).2
  have hsum : (term.exponent : ℝ) + (Axis.originalS.exponent : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact add_pos (by exact_mod_cast positive)
      (by exact_mod_cast Axis.original_s_exponent)
  have hcomb : centre (term.exponent : ℝ) (Axis.originalS.exponent : ℝ)
      (term.centre i : ℝ) (Axis.originalS.centre i : ℝ) =
      (Axis.originalS.centre i : ℝ) := by
    rw [hcentre]
    unfold centre
    field_simp [hsum]
  unfold axisShape Axis.sPairRate Axis.originalCentre
  rw [Axis.original_s_powers i,hcomb,hcentre]
  simp

theorem low_pair_shape (term : Term) (x : Point)
    (hl : sourceLow term) (positive : 0 < term.exponent) :
    pairShape term Axis.originalS x =
      (term.weight : ℝ) * Axis.originalWeight *
        ∏ i : Fin 3,
          (x i-Axis.originalCentre i)^term.powers i *
            Real.exp (-(Axis.sPairRate term Axis.originalS) *
              (x i-Axis.originalCentre i)^2) := by
  unfold pairShape Axis.originalWeight
  rw [low_axis_shape term 0 (x 0) hl positive,
    low_axis_shape term 1 (x 1) hl positive,
    low_axis_shape term 2 (x 2) hl positive]
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,
    Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
