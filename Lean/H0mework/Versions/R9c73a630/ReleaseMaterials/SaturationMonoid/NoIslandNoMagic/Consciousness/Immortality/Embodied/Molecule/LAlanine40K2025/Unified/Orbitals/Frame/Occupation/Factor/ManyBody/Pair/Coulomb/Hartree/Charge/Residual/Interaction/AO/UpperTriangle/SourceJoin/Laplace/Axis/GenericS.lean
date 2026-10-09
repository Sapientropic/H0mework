import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SourceHeat

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceFiniteData
open MeasureTheory
noncomputable section

def sPowers (term : Term) : Prop := ∀ axis : Fin 3, term.powers axis = 0

def sPairRate (left right : Term) : ℝ :=
  (left.exponent : ℝ) + (right.exponent : ℝ)

def sPairCentre (left right : Term) : Point := fun axis =>
  centre (left.exponent : ℝ) (right.exponent : ℝ)
    (left.centre axis : ℝ) (right.centre axis : ℝ)

def sPairAttenuation (left right : Term) : ℝ :=
  ∏ axis : Fin 3,
    Real.exp (-((left.exponent : ℝ) * (right.exponent : ℝ) /
      sPairRate left right *
      ((left.centre axis : ℝ) - (right.centre axis : ℝ))^2))

def sPairCoefficient (left right : Term) : ℝ :=
  (left.weight : ℝ) * (right.weight : ℝ) * sPairAttenuation left right

theorem s_axis_shape (left right : Term) (axis : Fin 3) (x : ℝ)
    (hl : sPowers left) (hr : sPowers right) :
    axisShape left right axis x =
      Real.exp (-((left.exponent : ℝ) * (right.exponent : ℝ) /
        sPairRate left right *
        ((left.centre axis : ℝ) - (right.centre axis : ℝ))^2)) *
      Real.exp (-(sPairRate left right) *
        (x-sPairCentre left right axis)^2) := by
  unfold axisShape sPairRate sPairCentre
  rw [hl axis,hr axis]
  simp only [pow_zero,one_mul]

theorem s_pair_shape (left right : Term) (x : Point)
    (hl : sPowers left) (hr : sPowers right) :
    pairShape left right x = sPairCoefficient left right *
      ∏ axis : Fin 3,
        Real.exp (-(sPairRate left right) *
          (x axis-sPairCentre left right axis)^2) := by
  unfold pairShape sPairCoefficient sPairAttenuation
  rw [s_axis_shape left right 0 (x 0) hl hr,
    s_axis_shape left right 1 (x 1) hl hr,
    s_axis_shape left right 2 (x 2) hl hr]
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,
    Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  ring

theorem s_pair_rate_positive (left right : Term)
    (hl : 0 < left.exponent) (hr : 0 < right.exponent) :
    0 < sPairRate left right := by
  unfold sPairRate
  exact add_pos (by exact_mod_cast hl) (by exact_mod_cast hr)

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
