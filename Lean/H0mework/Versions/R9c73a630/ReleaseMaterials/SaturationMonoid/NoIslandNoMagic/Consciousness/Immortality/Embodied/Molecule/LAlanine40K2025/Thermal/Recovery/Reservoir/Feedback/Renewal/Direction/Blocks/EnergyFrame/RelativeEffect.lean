import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Measurement

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalized_observable_relative_error (A B : Matrix ι ι ℂ) :
    ‖(measurementScale A)⁻¹ • A-(measurementScale B)⁻¹ • B‖ ≤ 2*(‖A-B‖/measurementScale A) := by
  let a := measurementScale A
  let b := measurementScale B
  have ap : 0 < a := measurementScale_pos A
  have bp : 0 < b := measurementScale_pos B
  have diff : |b-a| ≤ ‖A-B‖ := by
    simpa only [abs_sub_comm] using measurement_scale_error A B
  have split : a⁻¹ • A-b⁻¹ • B = a⁻¹ • (A-B)+(a⁻¹-b⁻¹) • B := by module
  have inverse : |a⁻¹-b⁻¹| = |b-a|/(a*b) := by
    rw [inv_sub_inv ap.ne' bp.ne',abs_div,abs_mul,abs_of_pos ap,abs_of_pos bp]
  have first : a⁻¹*‖A-B‖ = ‖A-B‖/a := by ring
  have second : (|b-a|/(a*b))*‖B‖ ≤ ‖A-B‖/a := by
    have boundB : ‖B‖ ≤ b := by dsimp [b,measurementScale]; linarith
    have denom : 0 < a*b := mul_pos ap bp
    rw [div_mul_eq_mul_div,div_le_div_iff₀ denom ap]
    have h := mul_le_mul diff boundB (norm_nonneg _) (norm_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right h ap.le]
  rw [split]
  calc
    _ ≤ ‖a⁻¹ • (A-B)‖+‖(a⁻¹-b⁻¹) • B‖ := norm_add_le _ _
    _ = a⁻¹*‖A-B‖+(|b-a|/(a*b))*‖B‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos ap,inverse]
    _ ≤ _ := by linarith


theorem bounded_effect_relative_error (A B : Matrix ι ι ℂ) :
    ‖boundedEffect A-boundedEffect B‖ ≤ ‖A-B‖/measurementScale A := by
  have expression : boundedEffect A-boundedEffect B = (1/2 : ℝ) •
      ((measurementScale A)⁻¹ • A-(measurementScale B)⁻¹ • B) := by
    ext i j
    simp only [boundedEffect,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
    push_cast
    ring
  rw [expression,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  nlinarith [normalized_observable_relative_error A B]


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
