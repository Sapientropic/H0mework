import H0mework.Chemistry.LAlanineBandContinuation.Images
import H0mework.Chemistry.LAlanineBandGeometry.Immersion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter

open SourceGaussianModel ContinuousGradient ContinuousSeed WholeBandSource WholeBandGeometry
open WholeBandContinuation TrueFlowGeometry TrueFlowDifferential Matrix Set
open scoped Matrix
noncomputable section

def seedFlowDerivative (c : FullBandCell) (p : Point) : Point →L[ℝ] Point :=
  bandSeedDerivative (cellSegment c) (Geometry.Source.epsilon 0) p +
    (ContinuousLinearMap.proj 2).smulRight (sourceGradient (cellSeed c p))

theorem seedFlowDerivative_injective (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (positive : PositiveNormalReports c) (p : Point) (inside : p ∈ cellDomain c) :
    Function.Injective (seedFlowDerivative c p) := by
  apply (injective_iff_map_eq_zero (seedFlowDerivative c p)).mpr
  intro h zero
  have expansion :
      bandUDerivative (cellSegment c) (Geometry.Source.epsilon 0) p h • basisVector 0 +
        h 1 • basisVector 1 + h 2 • sourceGradient (cellSeed c p) = 0 := zero
  have transverse : 0 < seedNormal ⬝ᵥ sourceGradient (cellSeed c p) := by
    have source := actual_transverse c fields positive p inside 0 (by constructor <;> norm_num)
    rwa [rawFlow_starts] at source
  have normal := congrArg (fun v : Point => seedNormal ⬝ᵥ v) expansion
  have timeProduct : h 2 * (seedNormal ⬝ᵥ sourceGradient (cellSeed c p)) = 0 := by
    simpa only [dotProduct_add, dotProduct_smul, seedNormal_dot_basis, smul_zero,
      zero_add, dotProduct_zero, smul_eq_mul, mul_zero] using normal
  have timeZero : h 2 = 0 := (mul_eq_zero.mp timeProduct).resolve_right transverse.ne'
  rw [timeZero, zero_smul, add_zero] at expansion
  have coordinates := (seed_derivative_kernel_exact c p h inside).mp expansion
  funext i
  fin_cases i
  · exact coordinates.1
  · exact coordinates.2
  · exact timeZero

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
