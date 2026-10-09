import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.RawCoordinates

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem trace_normalized_difference (A B : Matrix ι ι ℂ) (ha : A.trace ≠ 0) (hb : B.trace ≠ 0) :
    A.trace⁻¹ • A-B.trace⁻¹ • B=
      A.trace⁻¹ • ((A-B)+(B.trace-A.trace) • (B.trace⁻¹ • B)) := by
  ext i j
  simp only [Matrix.smul_apply,Matrix.sub_apply,Matrix.add_apply,smul_eq_mul]
  field_simp
  ring

theorem trace_normalization_error (A B : Matrix ι ι ℂ) (L d : ℝ) (dpos : 0 ≤ d)
    (space : (Fintype.card ι : ℝ)*d < L) (mass : L ≤ ‖B.trace‖)
    (reference : ‖B.trace⁻¹ • B‖ ≤ 1) (distance : ‖A-B‖ ≤ d) :
    ‖A.trace⁻¹ • A-B.trace⁻¹ • B‖ ≤ (1+(Fintype.card ι : ℝ))*d/(L-(Fintype.card ι : ℝ)*d) := by
  have traceDistance : ‖B.trace-A.trace‖ ≤ (Fintype.card ι : ℝ)*d := by
    rw [← Matrix.trace_sub]
    have paid := Donor.trace_norm_bound (B-A)
    rw [norm_sub_rev] at paid
    exact paid.trans (mul_le_mul_of_nonneg_left distance (by positivity))
  have lower : L-(Fintype.card ι : ℝ)*d ≤ ‖A.trace‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub B.trace A.trace 0
    simp only [sub_zero] at triangle
    linarith
  have positive : 0 < L-(Fintype.card ι : ℝ)*d := by linarith
  have ha : A.trace ≠ 0 := norm_pos_iff.mp (positive.trans_le lower)
  have hb : B.trace ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by nlinarith [show (0 : ℝ) ≤ (Fintype.card ι : ℝ)*d by positivity]) mass)
  rw [trace_normalized_difference A B ha hb,norm_smul,norm_inv]
  have inner : ‖(A-B)+(B.trace-A.trace) • (B.trace⁻¹ • B)‖ ≤ (1+(Fintype.card ι : ℝ))*d := by
    calc
      _ ≤ ‖A-B‖+‖(B.trace-A.trace) • (B.trace⁻¹ • B)‖ := norm_add_le _ _
      _ = ‖A-B‖+‖B.trace-A.trace‖*‖B.trace⁻¹ • B‖ := by rw [norm_smul]
      _ ≤ d+((Fintype.card ι : ℝ)*d)*1 := by gcongr
      _ = _ := by ring
  have invBound := inv_anti₀ positive lower
  calc
    _ ≤ ‖A.trace‖⁻¹*((1+(Fintype.card ι : ℝ))*d) := mul_le_mul_of_nonneg_left inner (inv_nonneg.mpr (norm_nonneg _))
    _ ≤ (L-(Fintype.card ι : ℝ)*d)⁻¹*((1+(Fintype.card ι : ℝ))*d) := mul_le_mul_of_nonneg_right invBound (by positivity)
    _ = _ := by ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
