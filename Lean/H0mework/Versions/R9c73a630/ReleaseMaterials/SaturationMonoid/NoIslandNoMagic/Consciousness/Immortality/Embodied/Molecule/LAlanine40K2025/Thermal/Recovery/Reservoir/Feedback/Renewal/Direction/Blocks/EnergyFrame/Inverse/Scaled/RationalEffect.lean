import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Rational
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Lower
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Stability

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
open Collision Load.Source Measurement Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def rationalRegularizer : ℝ := cosineHat^2

theorem rational_regularizer_positive : 0 < rationalRegularizer := by
  unfold rationalRegularizer cosineHat sinePolynomial
  rw [nativeClockStep_exact]
  norm_num

theorem rational_regularizer_error : |regularizer-rationalRegularizer| ≤ (3/10^18 : ℝ) := cosine_square_error

theorem rational_effect_error : ‖scaledEffect regularizer core-scaledEffect rationalRegularizer rationalCore‖ ≤
    (1/10^17 : ℝ) := by
  apply (scaled_effect_stability regularizer rationalRegularizer regularizer_positive rational_regularizer_positive core rationalCore).trans
  apply (div_le_iff₀ (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg regularizer_positive (norm_nonneg core)))).mpr
  nlinarith [rational_core_error,rational_regularizer_error,scaled_core_lower,regularizer_positive]

theorem rational_core_hermitian : rationalCore.IsHermitian := by
  have env : (Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead).IsHermitian := by
    change _ᴴ = _
    simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,numeric_environment_hermitian.eq]
  change star rationalCore=rationalCore
  simp only [rationalCore,star_add,star_smul,star_sub,star_mul,star_neg,star_pow,Complex.star_def,Complex.conj_ofReal,Complex.conj_I,
    actual_numeric_load_hermitian.isSelfAdjoint.star_eq,numeric_projector_hermitian.isSelfAdjoint.star_eq,
    loadInteraction_hermitian.isSelfAdjoint.star_eq,env.isSelfAdjoint.star_eq]
  module

theorem source_rational_effect_error :
    ‖Quantum.conjugation installedLoadFrame (sourceMeasurementEffect loadTotalHamiltonian)-
      Quantum.conjugation numericFree (scaledEffect rationalRegularizer rationalCore)‖ ≤ (262/10^12 : ℝ) := by
  have delta : ‖Quantum.conjugation numericFree (scaledEffect regularizer core)-
      Quantum.conjugation numericFree (scaledEffect rationalRegularizer rationalCore)‖ ≤ (1/10^17 : ℝ) := by
    rw [← map_sub]
    have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint numericFree)
      (scaledEffect regularizer core-scaledEffect rationalRegularizer rationalCore)
    change ‖Quantum.conjugation numericFree (scaledEffect regularizer core-scaledEffect rationalRegularizer rationalCore)‖ = _ at same
    rw [same]
    exact rational_effect_error
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (Quantum.conjugation installedLoadFrame (sourceMeasurementEffect loadTotalHamiltonian))
    (Quantum.conjugation numericFree (scaledEffect regularizer core))
    (Quantum.conjugation numericFree (scaledEffect rationalRegularizer rationalCore))
  linarith [source_scaled_effect_error]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
