import H0mework.Chemistry.LAlanineRefinementDensity.GaussianModel

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
noncomputable section

def centre (alpha beta left right : ℝ) : ℝ :=
  (alpha * left + beta * right) / (alpha + beta)

theorem complete_square (alpha beta left right x : ℝ)
    (positive : alpha + beta ≠ 0) :
    alpha * (x - left)^2 + beta * (x - right)^2 =
      (alpha + beta) * (x - centre alpha beta left right)^2 +
        alpha * beta / (alpha + beta) * (left - right)^2 := by
  unfold centre
  field_simp [positive]
  ring

theorem exponential_product (alpha beta left right x : ℝ)
    (positive : alpha + beta ≠ 0) :
    Real.exp (-alpha * (x - left)^2) *
      Real.exp (-beta * (x - right)^2) =
      Real.exp (-(alpha * beta / (alpha + beta) * (left - right)^2)) *
        Real.exp (-(alpha + beta) *
          (x - centre alpha beta left right)^2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  nlinarith [complete_square alpha beta left right x positive]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
