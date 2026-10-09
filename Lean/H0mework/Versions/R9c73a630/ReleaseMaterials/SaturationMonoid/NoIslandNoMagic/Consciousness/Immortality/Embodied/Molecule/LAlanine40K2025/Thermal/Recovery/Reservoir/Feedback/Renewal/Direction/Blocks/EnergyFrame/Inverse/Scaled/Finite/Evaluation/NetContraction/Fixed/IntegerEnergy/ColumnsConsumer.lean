import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ColumnsCertificate
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SharpColumns.Consumer
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem literal_first_pointer_actual_error :
    ‖value (fromTable literalFirstPointerTable pointerFin pointerFin)-
      PCExecution.pointer.submatrix
        (ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide))
        (ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (1/10^16 : ℝ) := by
  rw [literal_first_pointer_original]
  exact source_first_pointer_actual_error

theorem literal_first_columns_actual_error :
    ‖value (fromTable literalFirstColumnsTable pointerFin nativeFin)-
      sourceColumns (s((0 : Basis),1))
        (ordinaryFullEquiv (0 : Basis) 1 (by decide)) ordinaryInjection‖ ≤
      (3/10^16 : ℝ) := by
  rw [literal_first_columns_original,← ordinary_source_columns_value]
  exact source_first_columns_q_error_sharp

theorem literal_first_selected_nonzero :
    (literalFirstColumnsTable.re.get
      (pointerFin (.inl (.inr ((0,0),1),0)))).get (nativeFin ((0,1),0)) ≠ 0 := by
  decide +kernel

theorem literal_first_wrong_role_zero :
    (literalFirstColumnsTable.re.get
      (pointerFin (.inl (.inl ((0,0),0),0)))).get (nativeFin ((0,1),0)) = 0 := by
  decide +kernel

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
