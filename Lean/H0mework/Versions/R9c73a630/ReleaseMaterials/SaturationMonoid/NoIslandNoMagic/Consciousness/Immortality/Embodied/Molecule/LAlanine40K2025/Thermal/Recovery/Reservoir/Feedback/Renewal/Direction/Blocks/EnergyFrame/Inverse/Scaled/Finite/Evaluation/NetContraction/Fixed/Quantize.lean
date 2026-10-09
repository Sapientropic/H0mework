import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Rational
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Error

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem quantize_scalar_error (z : ℚ) :
    |(quantizeScalar z : ℝ)/(scale : ℝ)-(z : ℝ)| ≤ (1/(2*10^30) : ℝ) := by
  have dp : (0 : Int) < z.den := by exact_mod_cast z.den_pos
  have dr : (0 : ℝ) < z.den := by exact_mod_cast z.den_pos
  have sr : (0 : ℝ) < scale := by exact_mod_cast scale_positive
  have h := round_ratio_error (scale*z.num) z.den dp
  have hr : (2 : ℝ)*|(scale : ℝ)*(z.num : ℝ)-(z.den : ℝ)*(quantizeScalar z : ℝ)| ≤ z.den := by
    exact_mod_cast h
  have source : (z : ℝ)=(z.num : ℝ)/(z.den : ℝ) := Rat.cast_def z
  have same : (quantizeScalar z : ℝ)/(scale : ℝ)-(z : ℝ)=
      -((scale : ℝ)*(z.num : ℝ)-(z.den : ℝ)*(quantizeScalar z : ℝ))/((scale : ℝ)*(z.den : ℝ)) := by
    rw [source]
    field_simp
    ring
  rw [same,abs_div,abs_neg,abs_of_pos (mul_pos sr dr),div_le_iff₀ (mul_pos sr dr)]
  norm_num [scale] at hr ⊢
  nlinarith

theorem quantize_entry_error {α β : Type*} (A : MatrixQ α β) (i : α) (j : β) :
    ‖(value (quantize A)-qvalue A) i j‖ ≤ (1/10^30 : ℝ) := by
  have split : (value (quantize A)-qvalue A) i j=
      (((quantizeScalar (A i j).1 : ℝ)/(scale : ℝ)-((A i j).1 : ℝ) : ℝ) : ℂ)+
        Complex.I*((((quantizeScalar (A i j).2 : ℝ)/(scale : ℝ)-((A i j).2 : ℝ) : ℝ) : ℂ)) := by
    simp only [value,quantize,qvalue,raw,Scalar.value,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_ratCast]
    ring
  rw [split]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  linarith [quantize_scalar_error (A i j).1,quantize_scalar_error (A i j).2]

theorem quantize_error {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (A : MatrixQ α β)
    (rows : Fintype.card α ≤ 64) (cols : Fintype.card β ≤ 64) :
    ‖value (quantize A)-qvalue A‖ ≤ (64/10^30 : ℝ) := by
  simpa only [mul_one_div] using norm_from_entries _ (1/10^30) (by norm_num) rows cols (quantize_entry_error A)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
