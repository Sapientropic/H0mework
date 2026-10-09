import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.GibbsMass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Normalization
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.ExponentialComparison

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def spectralBath : Matrix Basis Basis ℂ := normalizedExponential E

theorem transformed_original_norm : ‖transformedOriginal‖ ≤ 20 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub transformedOriginal E 0
  simp only [sub_zero] at triangle
  have paid : ‖transformedOriginal-E‖ ≤ (21/10^12 : ℝ) := actual_source_diagonal_error
  linarith [diagonal_norm]

theorem original_exponential_error : ‖NormedSpace.exp (-transformedOriginal)-NormedSpace.exp (-E)‖ ≤ (1/50 : ℝ) :=
  Phase.source_exponential_comparison _ _ transformed_original_norm (diagonal_norm.trans (by norm_num)) actual_source_diagonal_error

theorem original_spectral_bath_error : ‖normalizedExponential transformedOriginal-spectralBath‖ ≤ (4/10^8 : ℝ) := by
  have mass : (60000000 : ℝ) ≤ ‖(NormedSpace.exp (-E)).trace‖ := by
    have positive : 0 ≤ referencePartition := le_trans (by norm_num) reference_partition_lower
    simpa [reference_exponential_trace,abs_of_nonneg positive] using reference_partition_lower
  have paid := trace_normalization_error (NormedSpace.exp (-transformedOriginal)) (NormedSpace.exp (-E))
    60000000 (1/50) (by norm_num) (by norm_num [Basis]) mass reference_gibbs_norm original_exponential_error
  exact paid.trans (by norm_num [Basis])

theorem original_calculated_bath_error : ‖Quantum.conjugation originalToCalculated Thermal.Source.bathCurrent-spectralBath‖ ≤ (4/10^8 : ℝ) := by
  rw [calculated_bath_exponential]
  exact original_spectral_bath_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
