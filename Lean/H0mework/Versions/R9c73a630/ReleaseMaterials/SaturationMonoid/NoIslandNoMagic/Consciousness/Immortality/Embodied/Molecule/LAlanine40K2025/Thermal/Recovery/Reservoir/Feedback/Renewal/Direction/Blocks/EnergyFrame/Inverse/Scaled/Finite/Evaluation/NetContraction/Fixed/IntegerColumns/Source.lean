import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerColumns.Error
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix BigOperators Matrix.Norms.L2Operator

theorem source_first_pointer_columns_error :
    ‖value sourceFirstPointerColumnsInt-
      qvalue ((ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide)).submatrix id Sum.inl)‖ ≤
      (7/10^15 : ℝ) := by
  rw [sourceFirstPointerColumnsInt,value_submatrix,qvalue_submatrix]
  have h := submatrix_error_le (value sourceFirstPointerInt)
    (qvalue (ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide)))
    id Sum.inl (by norm_num [OrdinaryFull]) (by norm_num [OrdinaryFull])
    _ source_first_pointer_int_error
  exact h.trans (by norm_num)

theorem source_first_supply_charged_error :
    ‖value sourceFirstSupplyChargedInt-
      qvalue ((ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)).submatrix
        id ordinaryInjection)‖ ≤ (1/10^25 : ℝ) := by
  rw [sourceFirstSupplyChargedInt,value_submatrix,qvalue_submatrix]
  have source := quantize_error
    (ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide))
    (by norm_num [OrdinaryFull]) (by norm_num [OrdinaryFull])
  have h := submatrix_error_le (value sourceFirstSupplyInt)
    (qvalue (ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)))
    id ordinaryInjection (by norm_num [OrdinaryFull]) (by norm_num)
    _ source
  exact h.trans (by norm_num)

theorem source_first_pointer_columns_norm :
    ‖qvalue ((ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide)).submatrix
      id Sum.inl)‖ ≤ (129 : ℝ) := by
  rw [qvalue_submatrix,← ordinary_pointer_source,qvalue_submatrix,Spec.pointer_value]
  change ‖PCExecution.pointer.submatrix
    (ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide))
    (fun j => ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide) (.inl j))‖ ≤ _
  have h := submatrix_norm_le64 PCExecution.pointer
    (ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide))
    (fun j => ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide) (.inl j))
    (by norm_num [OrdinaryFull]) (by norm_num [OrdinaryFull])
  exact h.trans (by nlinarith only [source_pointer_norm_sharp])

theorem source_first_supply_charged_norm :
    ‖qvalue ((ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)).submatrix
      id ordinaryInjection)‖ ≤ (129 : ℝ) := by
  rw [qvalue_submatrix,ordinary_supply_value]
  change ‖PCExecution.supply.submatrix
    (fun i => (ordinaryFullEquiv (0 : Basis) (1 : Basis) (by decide) i).val)
    (fun j => (ordinaryFullEquiv (0 : Basis) (1 : Basis) (by decide)
      (ordinaryInjection j)).val)‖ ≤ _
  have h := submatrix_norm_le64 PCExecution.supply
    (fun i => (ordinaryFullEquiv (0 : Basis) (1 : Basis) (by decide) i).val)
    (fun j => (ordinaryFullEquiv (0 : Basis) (1 : Basis) (by decide)
      (ordinaryInjection j)).val)
    (by norm_num [OrdinaryFull]) (by norm_num)
  exact h.trans (by nlinarith only [source_supply_norm_sharp])

theorem source_first_supply_charged_int_norm :
    ‖value sourceFirstSupplyChargedInt‖ ≤ (130 : ℝ) := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub (value sourceFirstSupplyChargedInt)
    (qvalue ((ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)).submatrix
      id ordinaryInjection)) 0
  simp only [sub_zero] at triangle
  linarith only [triangle,source_first_supply_charged_error,source_first_supply_charged_norm]

theorem source_first_columns_q_error :
    ‖value sourceFirstColumnsInt-
      qvalue (ordinarySourceColumnsQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (1/10^11 : ℝ) := by
  let A := qvalue ((ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide)).submatrix id Sum.inl)
  let B := qvalue ((ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)).submatrix
    id ordinaryInjection)
  have paid := rectangular_int_mul_error sourceFirstPointerColumnsInt
    sourceFirstSupplyChargedInt A B
    (by norm_num [OrdinaryFull]) (by norm_num)
    (7/10^15) (1/10^25)
    source_first_pointer_columns_error source_first_supply_charged_error
  change ‖value (multiply sourceFirstPointerColumnsInt sourceFirstSupplyChargedInt)-
    qvalue (qmultiply
      ((ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide)).submatrix id Sum.inl)
      ((ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)).submatrix
        id ordinaryInjection))‖ ≤ _
  rw [qvalue_multiply]
  apply paid.trans
  calc
    (64/10^30 : ℝ)+(7/10^15)*(‖B‖+1/10^25)+‖A‖*(1/10^25) ≤
      (64/10^30 : ℝ)+(7/10^15)*(129+1/10^25)+129*(1/10^25) := by
        gcongr
        · exact source_first_supply_charged_norm
        · exact source_first_pointer_columns_norm
    _ ≤ 1/10^11 := by norm_num

theorem source_first_columns_actual_error :
    ‖value sourceFirstColumnsInt-
      sourceColumns (s((0 : Basis),1))
        (ordinaryFullEquiv (0 : Basis) 1 (by decide)) ordinaryInjection‖ ≤
      (1/10^11 : ℝ) := by
  rw [← ordinary_source_columns_value]
  exact source_first_columns_q_error
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
