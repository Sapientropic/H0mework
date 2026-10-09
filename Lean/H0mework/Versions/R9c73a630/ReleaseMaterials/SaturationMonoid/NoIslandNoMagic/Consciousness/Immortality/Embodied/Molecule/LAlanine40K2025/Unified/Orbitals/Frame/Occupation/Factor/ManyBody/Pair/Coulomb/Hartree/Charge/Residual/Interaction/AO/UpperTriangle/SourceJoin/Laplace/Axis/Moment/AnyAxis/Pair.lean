import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.GenericS

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
noncomputable section

theorem p_axis_shape (axis : Fin 3) (term : Term) (i : Fin 3) (x : ℝ)
    (hp : sourcePAxis axis term) (positive : 0 < term.exponent) :
    axisShape term Axis.originalS i x =
      (x-Axis.originalCentre i)^term.powers i *
        Real.exp (-(Axis.sPairRate term Axis.originalS) *
          (x-Axis.originalCentre i)^2) := by
  have hcentre : term.centre i = Axis.originalS.centre i := hp.2.2 i
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

theorem p_axis_pair_shape (axis : Fin 3) (term : Term) (x : Point)
    (hp : sourcePAxis axis term) (positive : 0 < term.exponent) :
    pairShape term Axis.originalS x =
      (term.weight : ℝ) * Axis.originalWeight *
        (x axis-Axis.originalCentre axis) *
          ∏ i : Fin 3,
            Real.exp (-(Axis.sPairRate term Axis.originalS) *
              (x i-Axis.originalCentre i)^2) := by
  let P (i : Fin 3) : ℝ := (x i-Axis.originalCentre i)^term.powers i
  let E (i : Fin 3) : ℝ :=
    Real.exp (-(Axis.sPairRate term Axis.originalS) *
      (x i-Axis.originalCentre i)^2)
  have hP : (∏ i : Fin 3, P i) = x axis-Axis.originalCentre axis := by
    have hPi (i : Fin 3) :
        P i = if i = axis then x axis-Axis.originalCentre axis else 1 := by
      by_cases h : i = axis
      · subst i
        simp [P,hp.1]
      · simp [P,hp.2.1 i h,h]
    simp_rw [hPi]
    simp
  calc
    pairShape term Axis.originalS x =
        (term.weight : ℝ) * Axis.originalWeight *
          ∏ i : Fin 3, P i * E i := by
      unfold pairShape Axis.originalWeight
      rw [p_axis_shape axis term 0 (x 0) hp positive,
        p_axis_shape axis term 1 (x 1) hp positive,
        p_axis_shape axis term 2 (x 2) hp positive]
      simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,
        Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
      dsimp [P,E]
      ring
    _ = (term.weight : ℝ) * Axis.originalWeight *
          (∏ i : Fin 3, P i) * (∏ i : Fin 3, E i) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by rw [hP]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
