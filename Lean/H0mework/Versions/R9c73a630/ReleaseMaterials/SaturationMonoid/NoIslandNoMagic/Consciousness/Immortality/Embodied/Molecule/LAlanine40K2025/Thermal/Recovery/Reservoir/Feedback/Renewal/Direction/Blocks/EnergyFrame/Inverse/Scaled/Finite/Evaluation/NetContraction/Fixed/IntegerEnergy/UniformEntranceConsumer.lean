import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformEntranceSource
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_ordinary_received_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryReceivedInt a b ordered)-
      qvalue (ordinaryReceivedQ a b ordered)‖ ≤ (64/10^30 : ℝ) :=
  quantize_error _ (by norm_num [LoadPrimitive.NativeIndex])
    (by norm_num [LoadPrimitive.NativeIndex])

theorem source_ordinary_entrance_q_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryEntranceInt a b ordered)-
      qvalue (ordinaryEntranceQ a b ordered)‖ ≤ (4/10^16 : ℝ) := by
  let A := qvalue (ordinarySourceColumnsQ a b ordered)
  let B := qvalue (ordinaryReceivedQ a b ordered)
  have paid := rectangular_int_mul_error (sourceOrdinaryColumnsInt a b ordered)
    (sourceOrdinaryReceivedInt a b ordered) A B
    (by norm_num [OrdinaryFull]) (by norm_num [LoadPrimitive.NativeIndex])
    (3/10^16) (64/10^30)
    (source_ordinary_columns_q_error a b ordered)
    (source_ordinary_received_error a b ordered)
  change ‖value (multiply (sourceOrdinaryColumnsInt a b ordered)
    (sourceOrdinaryReceivedInt a b ordered))-
    qvalue (qmultiply (ordinarySourceColumnsQ a b ordered)
      (ordinaryReceivedQ a b ordered))‖ ≤ _
  rw [qvalue_multiply]
  apply paid.trans
  calc
    (64/10^30 : ℝ)+(3/10^16)*(‖B‖+64/10^30)+‖A‖*(64/10^30) ≤
      (64/10^30 : ℝ)+(3/10^16)*(1001/1000+64/10^30)+5*(64/10^30) := by
        gcongr
        · exact source_ordinary_received_norm a b ordered
        · exact source_ordinary_columns_norm a b ordered
    _ ≤ 4/10^16 := by norm_num

theorem source_ordinary_entrance_actual_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryEntranceInt a b ordered)-
      entranceColumns (s(a,b)) (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
        (ordinaryFullEquiv a b ordered.ne) ordinaryInjection‖ ≤
      (4/10^16 : ℝ) := by
  rw [← ordinary_entrance_value]
  exact source_ordinary_entrance_q_error a b ordered

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
