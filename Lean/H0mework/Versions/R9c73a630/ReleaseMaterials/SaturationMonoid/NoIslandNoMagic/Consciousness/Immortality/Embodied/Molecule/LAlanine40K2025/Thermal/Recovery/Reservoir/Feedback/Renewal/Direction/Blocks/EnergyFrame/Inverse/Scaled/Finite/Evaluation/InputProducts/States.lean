import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.SystemMiddle.Producer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.SystemFinal.Producer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.BathMiddle.Producer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.BathFinal.Producer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution.Consumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface Collision Load.Source Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem system_error : ‖Field.computedSystem-system‖ ≤ (5/10^22 : ℝ) := by
  have transported : ‖(Field.computedSystemWord*Dense.computedBase)*star Field.computedSystemWord-
      systemMiddle*star Field.computedSystemWord‖ ≤ (4/10^22 : ℝ) := by
    rw [← Matrix.sub_mul]
    have h := system_middle_actual_error
    rw [norm_sub_rev] at h
    exact (norm_mul_le _ _).trans ((mul_le_mul h (by simpa only [norm_star] using Field.computed_system_word_norm)
      (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have triangle := norm_sub_le_norm_sub_add_norm_sub Field.computedSystem (systemMiddle*star Field.computedSystemWord) system
  have last := system_final_actual_error
  rw [norm_sub_rev] at last
  exact triangle.trans ((add_le_add transported last).trans (by norm_num))

theorem bath_error : ‖Field.computedBath-bath‖ ≤ (4/10^22 : ℝ) := by
  have transported : ‖(Field.computedPolynomial*Diagonal.computedGibbs)*star Field.computedPolynomial-
      bathMiddle*star Field.computedPolynomial‖ ≤ (3/10^22 : ℝ) := by
    rw [← Matrix.sub_mul]
    have h := bath_middle_actual_error
    rw [norm_sub_rev] at h
    exact (norm_mul_le _ _).trans ((mul_le_mul h (by simpa only [norm_star] using Field.computed_polynomial_norm)
      (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have triangle := norm_sub_le_norm_sub_add_norm_sub Field.computedBath (bathMiddle*star Field.computedPolynomial) bath
  have last := bath_final_actual_error
  rw [norm_sub_rev] at last
  exact triangle.trans ((add_le_add transported last).trans (by norm_num))

theorem old_bath_norm : ‖Field.computedBath‖ ≤ 3 :=
  (PCExecution.close_norm _ _ _ _ Diagonal.computed_bath_norm Field.bath_numeric_error).trans (by norm_num)

theorem system_norm : ‖system‖ ≤ 4 :=
  (PCExecution.close_norm _ _ _ _ Field.computed_system_norm system_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
