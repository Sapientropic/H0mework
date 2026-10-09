import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformColumnsSource
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_ordinary_pointer_columns_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryPointerColumnsInt a b ordered)-
      qvalue ((ordinaryPointerQ a b ordered).submatrix id Sum.inl)‖ ≤
      (1/10^16 : ℝ) := by
  rw [sourceOrdinaryPointerColumnsInt,value_submatrix,qvalue_submatrix]
  change ‖(value (sourceOrdinaryPointerInt a b ordered)-
    qvalue (ordinaryPointerQ a b ordered)).submatrix id Sum.inl‖ ≤ _
  have paid := source_ordinary_pointer_actual_error a b ordered
  have same : qvalue (ordinaryPointerQ a b ordered)=
      PCExecution.pointer.submatrix (ordinaryPointerAddress a b ordered)
        (ordinaryPointerAddress a b ordered) := by
    rw [← ordinary_pointer_source,qvalue_submatrix,Spec.pointer_value]
  rw [← same] at paid
  exact (submatrix_columns_norm_le _ Sum.inl Sum.inl_injective).trans paid

theorem source_ordinary_supply_charged_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinarySupplyChargedInt a b ordered)-
      qvalue ((ordinarySupplyQ a b ordered).submatrix id ordinaryInjection)‖ ≤
      (64/10^30 : ℝ) := by
  rw [sourceOrdinarySupplyChargedInt,value_submatrix,qvalue_submatrix]
  change ‖(value (sourceOrdinarySupplyInt a b ordered)-
    qvalue (ordinarySupplyQ a b ordered)).submatrix id ordinaryInjection‖ ≤ _
  exact (submatrix_columns_norm_le _ ordinaryInjection
    source_ordinary_injection_injective).trans
    (quantize_error _ (by norm_num [OrdinaryFull]) (by norm_num [OrdinaryFull]))

theorem source_ordinary_columns_q_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryColumnsInt a b ordered)-
      qvalue (ordinarySourceColumnsQ a b ordered)‖ ≤ (3/10^16 : ℝ) := by
  let A := qvalue ((ordinaryPointerQ a b ordered).submatrix id Sum.inl)
  let B := qvalue ((ordinarySupplyQ a b ordered).submatrix id ordinaryInjection)
  have paid := rectangular_int_mul_error (sourceOrdinaryPointerColumnsInt a b ordered)
    (sourceOrdinarySupplyChargedInt a b ordered) A B
    (by norm_num [OrdinaryFull]) (by norm_num)
    (1/10^16) (64/10^30)
    (source_ordinary_pointer_columns_error a b ordered)
    (source_ordinary_supply_charged_error a b ordered)
  change ‖value (multiply (sourceOrdinaryPointerColumnsInt a b ordered)
    (sourceOrdinarySupplyChargedInt a b ordered))-
    qvalue (qmultiply ((ordinaryPointerQ a b ordered).submatrix id Sum.inl)
      ((ordinarySupplyQ a b ordered).submatrix id ordinaryInjection))‖ ≤ _
  rw [qvalue_multiply]
  apply paid.trans
  calc
    (64/10^30 : ℝ)+(1/10^16)*(‖B‖+64/10^30)+‖A‖*(64/10^30) ≤
      (64/10^30 : ℝ)+(1/10^16)*(2001/1000+64/10^30)+
        (2001/1000)*(64/10^30) := by
        gcongr
        · exact source_ordinary_supply_charged_norm a b ordered
        · exact source_ordinary_pointer_columns_norm a b ordered
    _ ≤ 3/10^16 := by norm_num

theorem source_ordinary_columns_actual_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryColumnsInt a b ordered)-
      sourceColumns (s(a,b)) (ordinaryFullEquiv a b ordered.ne)
        ordinaryInjection‖ ≤ (3/10^16 : ℝ) := by
  rw [← ordinary_source_columns_value]
  exact source_ordinary_columns_q_error a b ordered

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
