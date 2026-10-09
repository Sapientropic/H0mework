import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Coefficients
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Effect

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
open Collision Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def regularizer : ℝ := (Real.cos BasisInverse.actualAngle)^2

def core : LoadedJoint := numericLoadHamiltonian-(Real.sin BasisInverse.actualAngle : ℂ)^2 •
    Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead+
    (-(Real.sin BasisInverse.actualAngle : ℂ)^2-Complex.I*Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle) •
      (numericProjector*loadInteraction)+
    (-(Real.sin BasisInverse.actualAngle : ℂ)^2+Complex.I*Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle) •
      (loadInteraction*numericProjector)

theorem regularizer_positive : 0 < regularizer := by
  unfold regularizer
  exact sq_pos_of_pos (by linarith [source_cos_lower])

theorem core_original : core=(regularizer : ℂ) • numericCoreInverse := by
  have nonzero : (Real.cos BasisInverse.actualAngle : ℂ)^2 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith [source_cos_lower])))
  simp only [core,regularizer,Complex.ofReal_pow,numericCoreInverse,smul_add,smul_smul,
    mul_inv_cancel₀ nonzero,one_smul,plus_scaled,minus_scaled]

theorem core_hermitian : core.IsHermitian := by
  rw [core_original]
  exact numeric_core_hermitian.smul (by simp : star (regularizer : ℂ)=(regularizer : ℂ))

theorem numeric_effect_core : boundedEffect numericCoreInverse=scaledEffect regularizer core := by
  rw [core_original]
  exact original_scaled_effect regularizer regularizer_positive numericCoreInverse

theorem numeric_output_scaled_effect : boundedEffect numericOutput=
    Quantum.conjugation numericFree (scaledEffect regularizer core) := by
  rw [← numeric_effect_core,bounded_effect_conjugation]
  rfl

theorem source_scaled_effect_error :
    ‖Quantum.conjugation installedLoadFrame (sourceMeasurementEffect loadTotalHamiltonian)-
      Quantum.conjugation numericFree (scaledEffect regularizer core)‖ ≤ (261/10^12 : ℝ) := by
  rw [← numeric_output_scaled_effect]
  exact original_numeric_effect_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
