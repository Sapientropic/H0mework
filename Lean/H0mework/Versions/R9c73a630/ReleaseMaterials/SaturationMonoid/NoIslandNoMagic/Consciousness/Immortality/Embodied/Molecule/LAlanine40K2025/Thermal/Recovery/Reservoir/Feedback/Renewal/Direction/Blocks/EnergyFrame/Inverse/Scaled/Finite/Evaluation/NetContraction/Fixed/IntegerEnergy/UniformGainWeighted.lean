import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformGainSelected
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

private theorem ordinary_weighted_error (a b : Basis) (ordered : a < b)
    (VI : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2))
    (V : MatrixQ (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2))
    (e : ℝ) (inputError : ‖value VI-qvalue V‖ ≤ e)
    (inputNorm : ‖qvalue V‖ ≤ (24 : ℝ)) :
    ‖value (multiply (adjoint VI) (sourceOrdinaryPCInt a b))-
      (qvalue V)ᴴ*qvalue (ordinaryPCPointerQ a b)‖ ≤
      (64/10^30 : ℝ)+e*(89+64/10^30)+24*(64/10^30) := by
  have adjError : ‖value (adjoint VI)-(qvalue V)ᴴ‖ ≤ e := by
    rw [value_adjoint,← Matrix.conjTranspose_sub,Matrix.l2_opNorm_conjTranspose]
    exact inputError
  have paid := rectangular_int_mul_error (adjoint VI) (sourceOrdinaryPCInt a b)
    ((qvalue V)ᴴ) (qvalue (ordinaryPCPointerQ a b))
    (by norm_num) (by norm_num [OrdinaryFull]) e (64/10^30)
    adjError (source_ordinary_pc_int_error a b)
  have eNonnegative : 0 ≤ e := le_trans (norm_nonneg _) inputError
  apply paid.trans
  gcongr
  · exact source_ordinary_pc_norm a b ordered
  · simpa only [Matrix.l2_opNorm_conjTranspose] using inputNorm

theorem source_ordinary_weighted_errors (a b : Basis) (ordered : a < b) :
    ‖value (multiply (adjoint (sourceOrdinaryNineSelectedInt a b ordered))
        (sourceOrdinaryPCInt a b))-
      (qvalue ((ordinaryNineColumnsQ a b ordered).submatrix id chargedInjection))ᴴ *
        qvalue (ordinaryPCPointerQ a b)‖ ≤ (5/10^12 : ℝ) ∧
    ‖value (multiply (adjoint (sourceOrdinaryElevenSelectedInt a b ordered))
        (sourceOrdinaryPCInt a b))-
      (qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection))ᴴ *
        qvalue (ordinaryPCPointerQ a b)‖ ≤ (1/10^10 : ℝ) := by
  have selected := source_ordinary_selected_errors a b ordered
  have norm := source_ordinary_selected_norms_24 a b ordered
  constructor
  · have h := ordinary_weighted_error a b ordered
      (sourceOrdinaryNineSelectedInt a b ordered)
      ((ordinaryNineColumnsQ a b ordered).submatrix id chargedInjection)
      (4/10^14) selected.1 norm.1
    exact h.trans (by norm_num)
  · have h := ordinary_weighted_error a b ordered
      (sourceOrdinaryElevenSelectedInt a b ordered)
      ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection)
      (1/10^12) selected.2 norm.2
    exact h.trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
