import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SharpColumns.Source
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_first_pointer_columns_error_sharp :
    ‖value sourceFirstPointerColumnsInt-
      qvalue ((ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide)).submatrix
        id Sum.inl)‖ ≤ (1/10^16 : ℝ) := by
  rw [sourceFirstPointerColumnsInt,value_submatrix,qvalue_submatrix]
  change ‖(value sourceFirstPointerInt-
    qvalue (ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide))).submatrix
      id Sum.inl‖ ≤ _
  exact (submatrix_columns_norm_le _ Sum.inl Sum.inl_injective).trans
    source_first_pointer_int_error

theorem source_first_supply_charged_error_sharp :
    ‖value sourceFirstSupplyChargedInt-
      qvalue ((ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)).submatrix
        id ordinaryInjection)‖ ≤ (64/10^30 : ℝ) := by
  rw [sourceFirstSupplyChargedInt,value_submatrix,qvalue_submatrix]
  change ‖(value sourceFirstSupplyInt-
    qvalue (ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide))).submatrix
      id ordinaryInjection‖ ≤ _
  exact (submatrix_columns_norm_le _ ordinaryInjection
    source_ordinary_injection_injective).trans
    (quantize_error _ (by norm_num [OrdinaryFull]) (by norm_num [OrdinaryFull]))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
