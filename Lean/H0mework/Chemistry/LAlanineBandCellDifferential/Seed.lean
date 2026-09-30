import H0mework.Chemistry.LAlanineWholeBandCell0.GeometryCell0

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open SourceGaussianModel ContinuousGradient ContinuousSeed WholeBandGeometry WholeBandCell0Geometry
open TrueFlowGeometry WholeBandActual TrueFlowDifferential Matrix Set
open scoped Matrix
noncomputable section

theorem cell0_seed_width_positive (p : Cell0Point) :
    0 < bandWidth 0 (Geometry.Source.epsilon 0) (p.val 1) :=
  bandWidth_positive 0 _ _ source_epsilon_positive (cell_parameter_in_segment 0 p.val p.property)

def cell0_seedFlowDerivative (p : Cell0Point) : Point →L[ℝ] Point :=
  bandSeedDerivative 0 (Geometry.Source.epsilon 0) p.val +
    (ContinuousLinearMap.proj 2).smulRight (sourceGradient (cellSeed 0 p.val))

theorem cell0_seedFlowDerivative_injective (p : Cell0Point) : Function.Injective (cell0_seedFlowDerivative p) := by
  apply (injective_iff_map_eq_zero (cell0_seedFlowDerivative p)).mpr
  intro h zero
  have expansion :
      bandUDerivative 0 (Geometry.Source.epsilon 0) p.val h • basisVector 0 +
        h 1 • basisVector 1 + h 2 • sourceGradient (cellSeed 0 p.val) = 0 := zero
  have transverse : 0 < seedNormal ⬝ᵥ sourceGradient (cellSeed 0 p.val) := by
    have source := cell0_full_transverse p 0 (by constructor <;> norm_num)
    rw [rawFlow_starts] at source
    exact (by norm_num : (0 : ℝ) < 1/20).trans source
  have normal := congrArg (fun v : Point => seedNormal ⬝ᵥ v) expansion
  have timeProduct : h 2 * (seedNormal ⬝ᵥ sourceGradient (cellSeed 0 p.val)) = 0 := by
    simpa only [dotProduct_add, dotProduct_smul, seedNormal_dot_basis, smul_zero,
      zero_add, dotProduct_zero, smul_eq_mul, mul_zero] using normal
  have timeZero : h 2 = 0 := (mul_eq_zero.mp timeProduct).resolve_right transverse.ne'
  rw [timeZero, zero_smul, add_zero] at expansion
  have coefficients := seed_basis_coefficients _ _ expansion
  have alphaProduct : bandWidth 0 (Geometry.Source.epsilon 0) (p.val 1) * h 0 = 0 := by
    simpa [bandUDerivative, coefficients.2] using coefficients.1
  have alphaZero : h 0 = 0 := (mul_eq_zero.mp alphaProduct).resolve_left (cell0_seed_width_positive p).ne'
  funext i
  fin_cases i
  · exact alphaZero
  · exact coefficients.2
  · exact timeZero

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
