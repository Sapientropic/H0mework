import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Norm
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Error

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
noncomputable section

def sourceCoordinates (rho : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ :=
  Quantum.conjugation (star actualUnitary) rho

theorem actual_energy_error (rho : Matrix Basis Basis ℂ) (positive : rho.PosSemidef) :
    |energy A rho-energy E (sourceCoordinates rho)| ≤ (21/10^12 : ℝ)*rho.trace.re := by
  have both := Work.Capacity.energy_unitary_conjugation A rho (star actualUnitary)
  simp only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,star_star] at both
  have coordinates : sourceCoordinates rho = star (actualUnitary : Matrix Basis Basis ℂ)*rho*
      (actualUnitary : Matrix Basis Basis ℂ) := by
    simp only [sourceCoordinates,Quantum.conjugation_apply,Unitary.coe_star,star_star]
  rw [← coordinates] at both
  rw [← both,← Load.Producer.HeatProbability.energy_sub_left]
  have nonnegative : (sourceCoordinates rho).PosSemidef := Quantum.conjugation_posSemidef _ _ positive
  have bound := energy_norm_mass
    (star (actualUnitary : Matrix Basis Basis ℂ)*A*(actualUnitary : Matrix Basis Basis ℂ)-E)
    (sourceCoordinates rho) nonnegative
  have trace : (sourceCoordinates rho).trace = rho.trace := Quantum.conjugation_trace _ _
  rw [trace] at bound
  exact bound.trans (mul_le_mul_of_nonneg_right actual_source_diagonal_error
    (Complex.nonneg_iff.mp positive.trace_nonneg).1)

/-- The original analytic preparation, at its actual registered time, is consumed by the computed frame. -/
theorem actual_preparation_energy :
    |energy A (Preparation.preparedDensity (Preparation.collisionCurrentTime : ℝ))-
      energy E (sourceCoordinates (Preparation.preparedDensity (Preparation.collisionCurrentTime : ℝ)))| ≤
      (21/10^12 : ℝ) := by
  have bound := actual_energy_error _ (Preparation.preparedDensity_posSemidef (Preparation.collisionCurrentTime : ℝ))
  rw [Preparation.preparedDensity_trace] at bound
  simpa only [Complex.one_re,mul_one] using bound

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
