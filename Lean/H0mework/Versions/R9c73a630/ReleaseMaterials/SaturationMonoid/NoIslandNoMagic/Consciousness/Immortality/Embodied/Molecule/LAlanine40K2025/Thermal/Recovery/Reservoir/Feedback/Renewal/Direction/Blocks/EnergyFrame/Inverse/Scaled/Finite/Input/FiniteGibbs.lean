import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.GibbsComparison

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def gibbsNumeratorPolynomial : Matrix Basis Basis ℂ := (Phase.polynomial ((1/128 : ℝ) • (-E)) 14)^128
def finiteGibbs : Matrix Basis Basis ℂ := gibbsNumeratorPolynomial.trace⁻¹ • gibbsNumeratorPolynomial

theorem reference_exponential_polynomial_error :
    ‖NormedSpace.exp (-E)-gibbsNumeratorPolynomial‖ ≤ (2/10^6 : ℝ) := by
  have small := Phase.scaled_exponential_size E (diagonal_norm.trans (by norm_num))
  have step : ‖NormedSpace.exp ((1/128 : ℝ) • (-E))-Phase.polynomial ((1/128 : ℝ) • (-E)) 14‖ ≤ (1/10^18 : ℝ) :=
    (Phase.polynomial_error _ (5/32) (by norm_num) (by norm_num) small 14).trans (by norm_num [Nat.factorial])
  have first := Phase.small_exponential_norm _ small
  have second : ‖Phase.polynomial ((1/128 : ℝ) • (-E)) 14‖ ≤ (6/5 : ℝ) := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub (Phase.polynomial ((1/128 : ℝ) • (-E)) 14)
      (NormedSpace.exp ((1/128 : ℝ) • (-E))) 0
    simp only [sub_zero] at triangle
    rw [norm_sub_rev] at step
    linarith
  have paid := Phase.power_error _ _ (6/5) (1/10^18) (by norm_num) (by norm_num) (first.trans (by norm_num)) second step 128
  rw [Phase.exponential_128_parts (-E)]
  exact paid.trans (by norm_num)

theorem spectral_finite_gibbs_error : ‖spectralBath-finiteGibbs‖ ≤ (4/10^12 : ℝ) := by
  have mass : (60000000 : ℝ) ≤ ‖(NormedSpace.exp (-E)).trace‖ := by
    have positive : 0 ≤ referencePartition := le_trans (by norm_num) reference_partition_lower
    simpa [reference_exponential_trace,abs_of_nonneg positive] using reference_partition_lower
  have reverse : ‖gibbsNumeratorPolynomial-NormedSpace.exp (-E)‖ ≤ (2/10^6 : ℝ) := by
    rw [norm_sub_rev]
    exact reference_exponential_polynomial_error
  have paid := trace_normalization_error gibbsNumeratorPolynomial (NormedSpace.exp (-E))
    60000000 (2/10^6) (by norm_num) (by norm_num [Basis]) mass reference_gibbs_norm reverse
  rw [norm_sub_rev]
  exact paid.trans (by norm_num [Basis])

theorem original_finite_gibbs_error : ‖normalizedExponential transformedOriginal-finiteGibbs‖ ≤ (4001/10^11 : ℝ) := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub (normalizedExponential transformedOriginal) spectralBath finiteGibbs
  linarith [original_spectral_bath_error,spectral_finite_gibbs_error]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
