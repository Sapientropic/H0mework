import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Data.Block0
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Quadratic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def lowerVector : Fin 8 → ℚ := ![(-20224973347769/10000000000000000),(6532742358548218/10000000000000000),(-2706079863433956/10000000000000000),(-46/10000000000000000),(-20224973347871/10000000000000000),(-6532742358548251/10000000000000000),(2706079863433954/10000000000000000),(14/10000000000000000)]

theorem lower_mass_positive : 0 < testMass lowerVector := by decide +kernel

theorem lower_energy_checked : (480362644761/10^10 : ℚ)*testMass lowerVector ≤ -testEnergy real0 lowerVector := by
  decide +kernel

theorem block0_norm_lower : (480362644761/10^10 : ℝ) ≤ ‖block0‖ := by
  rw [← rational_block0]
  simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using norm_lower_from_test real0 imag0 lowerVector (480362644761/10^10) lower_mass_positive lower_energy_checked

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
