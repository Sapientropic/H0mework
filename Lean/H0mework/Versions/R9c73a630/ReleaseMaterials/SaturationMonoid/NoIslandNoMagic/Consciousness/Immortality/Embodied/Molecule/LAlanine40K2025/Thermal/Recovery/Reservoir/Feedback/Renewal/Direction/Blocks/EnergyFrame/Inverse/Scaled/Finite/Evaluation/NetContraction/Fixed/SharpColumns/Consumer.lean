import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SharpColumns.Error
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_first_columns_q_error_sharp :
    ‖value sourceFirstColumnsInt-
      qvalue (ordinarySourceColumnsQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (3/10^16 : ℝ) := by
  let A := qvalue ((ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide)).submatrix id Sum.inl)
  let B := qvalue ((ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)).submatrix
    id ordinaryInjection)
  have paid := rectangular_int_mul_error sourceFirstPointerColumnsInt
    sourceFirstSupplyChargedInt A B
    (by norm_num [OrdinaryFull]) (by norm_num)
    (1/10^16) (64/10^30)
    source_first_pointer_columns_error_sharp source_first_supply_charged_error_sharp
  change ‖value (multiply sourceFirstPointerColumnsInt sourceFirstSupplyChargedInt)-
    qvalue (qmultiply
      ((ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide)).submatrix id Sum.inl)
      ((ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)).submatrix
        id ordinaryInjection))‖ ≤ _
  rw [qvalue_multiply]
  apply paid.trans
  calc
    (64/10^30 : ℝ)+(1/10^16)*(‖B‖+64/10^30)+‖A‖*(64/10^30) ≤
      (64/10^30 : ℝ)+(1/10^16)*(2001/1000+64/10^30)+
        (2001/1000)*(64/10^30) := by
        gcongr
        · exact source_first_supply_charged_norm_sharp
        · exact source_first_pointer_columns_norm_sharp
    _ ≤ 3/10^16 := by norm_num

theorem source_first_columns_norm_sharp :
    ‖qvalue (ordinarySourceColumnsQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (5 : ℝ) := by
  rw [ordinarySourceColumnsQ,qvalue_multiply]
  have h := Matrix.l2_opNorm_mul
    (qvalue ((ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide)).submatrix id Sum.inl))
    (qvalue ((ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)).submatrix
      id ordinaryInjection))
  have product := mul_le_mul source_first_pointer_columns_norm_sharp
    source_first_supply_charged_norm_sharp (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 2001/1000)
  exact h.trans (by nlinarith only [product])

theorem source_first_entrance_q_error_sharp :
    ‖value sourceFirstEntranceInt-
      qvalue (ordinaryEntranceQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (4/10^16 : ℝ) := by
  let A := qvalue (ordinarySourceColumnsQ (0 : Basis) (1 : Basis) (by decide))
  let B := qvalue (ordinaryReceivedQ (0 : Basis) (1 : Basis) (by decide))
  have paid := rectangular_int_mul_error sourceFirstColumnsInt sourceFirstReceivedInt A B
    (by norm_num [OrdinaryFull]) (by norm_num [LoadPrimitive.NativeIndex])
    (3/10^16) (64/10^30)
    source_first_columns_q_error_sharp source_first_received_error
  change ‖value (multiply sourceFirstColumnsInt sourceFirstReceivedInt)-
    qvalue (qmultiply
      (ordinarySourceColumnsQ (0 : Basis) (1 : Basis) (by decide))
      (ordinaryReceivedQ (0 : Basis) (1 : Basis) (by decide)))‖ ≤ _
  rw [qvalue_multiply]
  apply paid.trans
  calc
    (64/10^30 : ℝ)+(3/10^16)*(‖B‖+64/10^30)+‖A‖*(64/10^30) ≤
      (64/10^30 : ℝ)+(3/10^16)*(1001/1000+64/10^30)+5*(64/10^30) := by
        gcongr
        · exact source_first_received_norm
        · exact source_first_columns_norm_sharp
    _ ≤ 4/10^16 := by norm_num

theorem source_first_entrance_norm_sharp :
    ‖qvalue (ordinaryEntranceQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (6 : ℝ) := by
  rw [ordinaryEntranceQ,qvalue_multiply]
  have h := Matrix.l2_opNorm_mul
    (qvalue (ordinarySourceColumnsQ (0 : Basis) (1 : Basis) (by decide)))
    (qvalue (ordinaryReceivedQ (0 : Basis) (1 : Basis) (by decide)))
  have product := mul_le_mul source_first_columns_norm_sharp source_first_received_norm
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 5)
  exact h.trans (by nlinarith only [product])

theorem source_first_entrance_actual_error_sharp :
    ‖value sourceFirstEntranceInt-
      entranceColumns (s((0 : Basis),1))
        (Scaled.Order.offDiagonalPCEEquiv (0 : Basis) 1 (by decide))
        (ordinaryFullEquiv (0 : Basis) 1 (by decide)) ordinaryInjection‖ ≤
      (4/10^16 : ℝ) := by
  rw [← ordinary_entrance_value]
  exact source_first_entrance_q_error_sharp

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
