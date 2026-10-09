import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformGainNorm
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_ordinary_selected_errors (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryNineSelectedInt a b ordered)-
      qvalue ((ordinaryNineColumnsQ a b ordered).submatrix id chargedInjection)‖ ≤
        (4/10^14 : ℝ) ∧
    ‖value (sourceOrdinaryElevenSelectedInt a b ordered)-
      qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection)‖ ≤
        (1/10^12 : ℝ) := by
  have nine := (source_ordinary_arms_actual a b ordered).1
  have eleven := (source_ordinary_arms_actual a b ordered).2
  rw [← ordinary_nine_columns_value a b ordered] at nine
  rw [← ordinary_eleven_columns_value a b ordered] at eleven
  constructor
  · rw [sourceOrdinaryNineSelectedInt,value_submatrix,qvalue_submatrix]
    change ‖(value (sourceOrdinaryNineInt a b ordered)-
      qvalue (ordinaryNineColumnsQ a b ordered)).submatrix id chargedInjection‖ ≤ _
    exact (submatrix_columns_norm_le _ chargedInjection
      charged_injection_injective).trans nine
  · rw [sourceOrdinaryElevenSelectedInt,value_submatrix,qvalue_submatrix]
    change ‖(value (sourceOrdinaryElevenInt a b ordered)-
      qvalue (ordinaryElevenColumnsQ a b ordered)).submatrix id chargedInjection‖ ≤ _
    exact (submatrix_columns_norm_le _ chargedInjection
      charged_injection_injective).trans eleven

theorem source_ordinary_pc_int_error (a b : Basis) :
    ‖value (sourceOrdinaryPCInt a b)-qvalue (ordinaryPCPointerQ a b)‖ ≤
      (64/10^30 : ℝ) :=
  quantize_error _ (by norm_num [OrdinaryFull]) (by norm_num [OrdinaryFull])

theorem source_ordinary_body_int_error (a b : Basis) :
    ‖value (sourceOrdinaryBodyInt a b)-
      qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)‖ ≤
      (64/10^30 : ℝ) :=
  quantize_error _ (by norm_num) (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
