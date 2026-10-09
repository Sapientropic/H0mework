import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEntrance.Base
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_first_received_error :
    ‖value sourceFirstReceivedInt-
      qvalue (ordinaryReceivedQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (64/10^30 : ℝ) :=
  quantize_error _ (by norm_num [LoadPrimitive.NativeIndex])
    (by norm_num [LoadPrimitive.NativeIndex])

theorem source_first_received_norm :
    ‖qvalue (ordinaryReceivedQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (1001/1000 : ℝ) := by
  let k := s((0 : Basis),(1 : Basis))
  have parent : ‖restrict pceOrbit k LoadExecution.receivedWord‖ ≤
      (1001/1000 : ℝ) :=
    ((norm_le_iff_block_norm_le received_preserves (1001/1000) (by norm_num)).mp
      source_received_word_norm_sharp) k
  have same : qvalue (ordinaryReceivedQ (0 : Basis) (1 : Basis) (by decide)) =
      (restrict pceOrbit k LoadExecution.receivedWord).submatrix
        (Scaled.Order.offDiagonalPCEEquiv (0 : Basis) (1 : Basis) (by decide))
        (Scaled.Order.offDiagonalPCEEquiv (0 : Basis) (1 : Basis) (by decide)) := by
    rw [ordinaryReceivedQ_value]
    simp only [restrict,Matrix.submatrix_submatrix]
    have address : (Subtype.val ∘ (Scaled.Order.offDiagonalPCEEquiv
        (0 : Basis) (1 : Basis) (by decide) :
          LoadPrimitive.NativeIndex ≃ BodyFiber k)) =
          Scaled.Order.orbitPCE (0 : Basis) (1 : Basis) := rfl
    rw [address]
  rw [same,Finite.reindex_norm]
  exact parent

theorem source_first_columns_norm :
    ‖qvalue (ordinarySourceColumnsQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (16700 : ℝ) := by
  rw [ordinarySourceColumnsQ,qvalue_multiply]
  have h := Matrix.l2_opNorm_mul
    (qvalue ((ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide)).submatrix id Sum.inl))
    (qvalue ((ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)).submatrix
      id ordinaryInjection))
  have product := mul_le_mul source_first_pointer_columns_norm
    source_first_supply_charged_norm (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 129)
  exact h.trans (by nlinarith only [product])

theorem source_first_entrance_q_error :
    ‖value sourceFirstEntranceInt-
      qvalue (qmultiply
        (ordinarySourceColumnsQ (0 : Basis) (1 : Basis) (by decide))
        (ordinaryReceivedQ (0 : Basis) (1 : Basis) (by decide)))‖ ≤
      (2/10^11 : ℝ) := by
  let A := qvalue (ordinarySourceColumnsQ (0 : Basis) (1 : Basis) (by decide))
  let B := qvalue (ordinaryReceivedQ (0 : Basis) (1 : Basis) (by decide))
  have paid := rectangular_int_mul_error sourceFirstColumnsInt sourceFirstReceivedInt A B
    (by norm_num [OrdinaryFull]) (by norm_num [LoadPrimitive.NativeIndex])
    (1/10^11) (64/10^30) source_first_columns_q_error source_first_received_error
  change ‖value (multiply sourceFirstColumnsInt sourceFirstReceivedInt)-
    qvalue (qmultiply (ordinarySourceColumnsQ (0 : Basis) (1 : Basis) (by decide))
      (ordinaryReceivedQ (0 : Basis) (1 : Basis) (by decide)))‖ ≤ _
  rw [qvalue_multiply]
  apply paid.trans
  calc
    (64/10^30 : ℝ)+(1/10^11)*(‖B‖+64/10^30)+‖A‖*(64/10^30) ≤
      (64/10^30 : ℝ)+(1/10^11)*(1001/1000+64/10^30)+16700*(64/10^30) := by
        gcongr
        · exact source_first_received_norm
        · exact source_first_columns_norm
    _ ≤ 2/10^11 := by norm_num

theorem source_first_entrance_actual_error :
    ‖value sourceFirstEntranceInt-
      entranceColumns (s((0 : Basis),1))
        (Scaled.Order.offDiagonalPCEEquiv (0 : Basis) 1 (by decide))
        (ordinaryFullEquiv (0 : Basis) 1 (by decide)) ordinaryInjection‖ ≤
      (2/10^11 : ℝ) := by
  rw [← ordinary_entrance_value]
  exact source_first_entrance_q_error
end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
