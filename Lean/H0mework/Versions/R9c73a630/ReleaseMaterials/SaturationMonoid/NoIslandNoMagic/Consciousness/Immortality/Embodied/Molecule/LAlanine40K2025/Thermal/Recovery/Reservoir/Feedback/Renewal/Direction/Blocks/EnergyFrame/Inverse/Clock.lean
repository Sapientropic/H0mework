import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Output
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Propagation.Producer Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem source_clock_lower : (43/100000 : ℝ) < nativeClockStep := by
  rw [nativeClockStep_exact]
  norm_num

theorem source_cos_lower : (42/100000 : ℝ) < Real.cos BasisInverse.actualAngle := by
  rw [BasisInverse.actualAngle,Real.cos_pi_div_two_sub]
  have lower := source_clock_lower
  have upper := nativeClock_small.2
  have sine := Real.sin_ge_sub_cube nativeClock_small.1.le
  have cube := pow_le_pow_left₀ nativeClock_small.1.le upper.le 3
  nlinarith

theorem source_cos_inverse_square : ‖((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹‖ ≤ 6000000 := by
  rw [norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith [source_cos_lower])]
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith [source_cos_lower]))).mpr
  nlinarith [source_cos_lower]

theorem source_sin_square : ‖(Real.sin BasisInverse.actualAngle : ℂ)^2‖ ≤ 1 := by
  rw [norm_pow,Complex.norm_real,Real.norm_eq_abs]
  nlinarith [Real.abs_sin_le_one BasisInverse.actualAngle,abs_nonneg (Real.sin BasisInverse.actualAngle)]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
