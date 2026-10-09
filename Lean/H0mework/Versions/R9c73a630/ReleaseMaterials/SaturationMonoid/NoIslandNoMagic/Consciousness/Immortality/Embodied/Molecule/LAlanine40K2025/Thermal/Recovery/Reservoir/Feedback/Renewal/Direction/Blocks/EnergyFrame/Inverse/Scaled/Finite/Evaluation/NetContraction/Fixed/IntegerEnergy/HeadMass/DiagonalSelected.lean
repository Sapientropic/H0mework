import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.DiagonalPulse
set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Collision Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_diagonal_charged_select_injective : Function.Injective diagonalChargedSelect := by
  intro i j h
  exact congrArg Prod.snd h

theorem source_diagonal_selected_norms (a : Basis) (different : a ≠ 97) :
    ‖qvalue (sourceDiagonalNineSelectedQ a different)‖ ≤ (384 : ℝ) ∧
    ‖qvalue (sourceDiagonalElevenSelectedQ a different)‖ ≤ (6144 : ℝ) := by
  constructor
  · rw [sourceDiagonalNineSelectedQ,qvalue_submatrix]
    exact (submatrix_columns_norm_le _ diagonalChargedSelect
      source_diagonal_charged_select_injective).trans
        (source_diagonal_nine_norm a different)
  · rw [sourceDiagonalElevenSelectedQ,qvalue_submatrix]
    exact (submatrix_columns_norm_le _ diagonalChargedSelect
      source_diagonal_charged_select_injective).trans
        (source_diagonal_eleven_norm a different)

theorem source_diagonal_selected_errors (a : Basis) (different : a ≠ 97) :
    ‖value (sourceDiagonalNineSelectedInt a different)-
      qvalue (sourceDiagonalNineSelectedQ a different)‖ ≤ (2/10^25 : ℝ) ∧
    ‖value (sourceDiagonalElevenSelectedInt a different)-
      qvalue (sourceDiagonalElevenSelectedQ a different)‖ ≤ (5/10^24 : ℝ) := by
  constructor
  · rw [sourceDiagonalNineSelectedInt,sourceDiagonalNineSelectedQ]
    simp only [value_submatrix,qvalue_submatrix]
    change ‖(value (sourceDiagonalNineInt a different)-
      qvalue (nineColumnsQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
        (diagonalFullEquiv a different) diagonalInjection)).submatrix id
          diagonalChargedSelect‖ ≤ _
    exact (submatrix_columns_norm_le _ diagonalChargedSelect
      source_diagonal_charged_select_injective).trans
        (source_diagonal_nine_error a different)
  · rw [sourceDiagonalElevenSelectedInt,sourceDiagonalElevenSelectedQ]
    simp only [value_submatrix,qvalue_submatrix]
    change ‖(value (sourceDiagonalElevenInt a different)-
      qvalue (elevenColumnsQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
        (diagonalFullEquiv a different) diagonalInjection)).submatrix id
          diagonalChargedSelect‖ ≤ _
    exact (submatrix_columns_norm_le _ diagonalChargedSelect
      source_diagonal_charged_select_injective).trans
        (source_diagonal_eleven_error a different)

theorem source_diagonal_pc_int_error (a : Basis) (different : a ≠ 97) :
    ‖value (sourceDiagonalPCInt a different)-
      qvalue (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))‖ ≤
      (64/10^30 : ℝ) :=
  quantize_error _ (by norm_num [DiagonalFull]) (by norm_num [DiagonalFull])

theorem source_diagonal_body_int_error (a : Basis) :
    ‖value (sourceDiagonalBodyInt a)-
      qvalue (qscale (pairQ (a,a) (a,a)) environmentQ)‖ ≤
      (64/10^30 : ℝ) :=
  quantize_error _ (by norm_num) (by norm_num)

theorem source_diagonal_body_norm (a : Basis) :
    ‖qvalue (qscale (pairQ (a,a) (a,a)) environmentQ)‖ ≤ (10 : ℝ) := by
  rw [qvalue_scale,environmentQ_value]
  have pairNorm : ‖InputProducts.pair‖ ≤ (5 : ℝ) := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub InputProducts.pair
      Field.computedPair 0
    simp only [sub_zero] at triangle
    rw [norm_sub_rev] at triangle
    linarith only [triangle,InputProducts.pair_error,PCExecution.field_pair_norm]
  have entry : ‖Scalar.value (pairQ (a,a) (a,a))‖ ≤ (5 : ℝ) := by
    have pairValue : Scalar.value (pairQ (a,a) (a,a))=
        InputProducts.pair (a,a) (a,a) :=
      congrFun (congrFun pairQ_value (a,a)) (a,a)
    rw [pairValue]
    exact (matrix_entry_norm_le InputProducts.pair (a,a) (a,a)).trans pairNorm
  rw [norm_smul]
  exact (mul_le_mul entry Diagonal.finite_environment_norm
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
