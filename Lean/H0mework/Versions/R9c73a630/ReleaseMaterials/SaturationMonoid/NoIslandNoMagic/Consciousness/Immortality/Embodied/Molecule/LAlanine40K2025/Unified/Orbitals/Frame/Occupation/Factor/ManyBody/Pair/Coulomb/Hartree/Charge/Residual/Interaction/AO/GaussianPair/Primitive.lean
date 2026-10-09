import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Algebra

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement SourceGaussianModel
open BasinRefinement.GaussianPrimitive
noncomputable section

theorem factor_zero (alpha : ℚ) (power : ℕ) (x : ℝ) :
    factor alpha power 0 x = x^power * Real.exp (-(alpha : ℝ) * x^2) := by
  simp [factor,jetPoly,gaussian]

def axisShape (left right : Term) (axis : Fin 3) (x : ℝ) : ℝ :=
  (x - (left.centre axis : ℝ)) ^ left.powers axis *
    (x - (right.centre axis : ℝ)) ^ right.powers axis *
    Real.exp (-((left.exponent : ℝ) * (right.exponent : ℝ) /
      ((left.exponent : ℝ) + (right.exponent : ℝ)) *
      ((left.centre axis : ℝ) - (right.centre axis : ℝ))^2)) *
    Real.exp (-((left.exponent : ℝ) + (right.exponent : ℝ)) *
      (x - centre (left.exponent : ℝ) (right.exponent : ℝ)
        (left.centre axis : ℝ) (right.centre axis : ℝ))^2)

theorem factor_pair (left right : Term) (axis : Fin 3) (x : ℝ)
    (positive : (left.exponent : ℝ) + (right.exponent : ℝ) ≠ 0) :
    factor left.exponent (left.powers axis) 0 (x - left.centre axis) *
      factor right.exponent (right.powers axis) 0 (x - right.centre axis) =
      axisShape left right axis x := by
  rw [factor_zero,factor_zero]
  calc
    _ = ((x - (left.centre axis : ℝ)) ^ left.powers axis *
          (x - (right.centre axis : ℝ)) ^ right.powers axis) *
        (Real.exp (-(left.exponent : ℝ) * (x - left.centre axis)^2) *
          Real.exp (-(right.exponent : ℝ) * (x - right.centre axis)^2)) := by ring
    _ = ((x - (left.centre axis : ℝ)) ^ left.powers axis *
          (x - (right.centre axis : ℝ)) ^ right.powers axis) *
        (Real.exp (-((left.exponent : ℝ) * (right.exponent : ℝ) /
          ((left.exponent : ℝ) + (right.exponent : ℝ)) *
          ((left.centre axis : ℝ) - (right.centre axis : ℝ))^2)) *
          Real.exp (-((left.exponent : ℝ) + (right.exponent : ℝ)) *
            (x - centre (left.exponent : ℝ) (right.exponent : ℝ)
              (left.centre axis : ℝ) (right.centre axis : ℝ))^2)) := by
      rw [exponential_product (left.exponent : ℝ) (right.exponent : ℝ)
        (left.centre axis : ℝ) (right.centre axis : ℝ) x positive]
    _ = _ := by unfold axisShape; ring

def pairShape (left right : Term) (x : Point) : ℝ :=
  (left.weight : ℝ) * (right.weight : ℝ) *
    axisShape left right 0 (x 0) *
    axisShape left right 1 (x 1) *
    axisShape left right 2 (x 2)

theorem value_pair (left right : Term) (x : Point)
    (positive : (left.exponent : ℝ) + (right.exponent : ℝ) ≠ 0) :
    value left (fun _ => 0) x * value right (fun _ => 0) x =
      pairShape left right x := by
  have axis0 := factor_pair left right 0 (x 0) positive
  have axis1 := factor_pair left right 1 (x 1) positive
  have axis2 := factor_pair left right 2 (x 2) positive
  unfold value pairShape
  simp only []
  calc
    _ = (left.weight : ℝ) * (right.weight : ℝ) *
        (factor left.exponent (left.powers 0) 0 (x 0 - left.centre 0) *
          factor right.exponent (right.powers 0) 0 (x 0 - right.centre 0)) *
        (factor left.exponent (left.powers 1) 0 (x 1 - left.centre 1) *
          factor right.exponent (right.powers 1) 0 (x 1 - right.centre 1)) *
        (factor left.exponent (left.powers 2) 0 (x 2 - left.centre 2) *
          factor right.exponent (right.powers 2) 0 (x 2 - right.centre 2)) := by ring
    _ = _ := by rw [axis0,axis1,axis2]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
