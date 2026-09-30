import H0mework.Chemistry.LAlanineBandGeometry.Cells
import H0mework.Chemistry.LAlanineParametric.SeedDerivative

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGeometry

open SourceGaussianModel ContinuousSeed WholeBandSource TrueFlowGeometry
noncomputable section

/-- The seed ignores flow time, but has no additional kernel on any source cell. -/
theorem seed_derivative_kernel_exact (c : FullBandCell) (p h : Point) (inside : p ∈ cellDomain c) :
    bandSeedDerivative (cellSegment c) (Geometry.Source.epsilon 0) p h = 0 ↔
      h 0 = 0 ∧ h 1 = 0 := by
  constructor
  · intro zero
    have expansion : bandUDerivative (cellSegment c) (Geometry.Source.epsilon 0) p h • basisVector 0 +
        h 1 • basisVector 1 = 0 := zero
    have coefficients := seed_basis_coefficients _ _ expansion
    have hwidth := bandWidth_positive (cellSegment c) (Geometry.Source.epsilon 0) (p 1)
      source_epsilon_positive (cell_parameter_in_segment c p inside)
    have product : bandWidth (cellSegment c) (Geometry.Source.epsilon 0) (p 1) * h 0 = 0 := by
      simpa [bandUDerivative, coefficients.2] using coefficients.1
    exact ⟨(mul_eq_zero.mp product).resolve_left hwidth.ne', coefficients.2⟩
  · rintro ⟨h0,h1⟩
    change bandUDerivative (cellSegment c) (Geometry.Source.epsilon 0) p h • basisVector 0 +
      h 1 • basisVector 1 = 0
    simp [bandUDerivative, h0, h1]

theorem seed_surface_derivative_injective (c : FullBandCell) (p : Point) (inside : p ∈ cellDomain c) :
    Function.Injective (fun v : Fin 2 → ℝ =>
      bandSeedDerivative (cellSegment c) (Geometry.Source.epsilon 0) p ![v 0,v 1,0]) := by
  intro a b same
  dsimp only at same
  have kernel : bandSeedDerivative (cellSegment c) (Geometry.Source.epsilon 0) p
      (![a 0,a 1,0] - ![b 0,b 1,0]) = 0 := by rw [map_sub, same, sub_self]
  have coordinates := (seed_derivative_kernel_exact c p _ inside).mp kernel
  funext i
  fin_cases i
  · exact sub_eq_zero.mp coordinates.1
  · exact sub_eq_zero.mp coordinates.2

end
end LAlanine40K2025.BasinRefinement.WholeBandGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
