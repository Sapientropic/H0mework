import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformPulseNorm
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

private theorem ordinary_pulse_int_error
    (P : MatrixQ (OrdinaryFull ⊕ OrdinaryFull) (OrdinaryFull ⊕ OrdinaryFull)) :
    ‖value (quantize P)-qvalue P‖ ≤ (64/10^30 : ℝ) :=
  quantize_error P (by norm_num [OrdinaryFull]) (by norm_num [OrdinaryFull])

private theorem ordinary_pulse_step_error
    (PI : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
      (OrdinaryFull ⊕ OrdinaryFull))
    (P : MatrixQ (OrdinaryFull ⊕ OrdinaryFull)
      (OrdinaryFull ⊕ OrdinaryFull))
    (VI : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) LoadPrimitive.NativeIndex)
    (V : MatrixQ (OrdinaryFull ⊕ OrdinaryFull) LoadPrimitive.NativeIndex)
    (e n : ℝ) (pulseError : ‖value PI-qvalue P‖ ≤ (64/10^30 : ℝ))
    (pulseNorm : ‖qvalue P‖ ≤ (4 : ℝ))
    (inputError : ‖value VI-qvalue V‖ ≤ e)
    (inputNorm : ‖qvalue V‖ ≤ n) :
    ‖value (multiply PI VI)-qvalue (qmultiply P V)‖ ≤
      (64/10^30 : ℝ)+(64/10^30 : ℝ)*(n+e)+4*e := by
  rw [qvalue_multiply]
  have h := rectangular_int_mul_error PI VI (qvalue P) (qvalue V)
    (by norm_num [OrdinaryFull]) (by norm_num [LoadPrimitive.NativeIndex])
    (64/10^30) e pulseError inputError
  have enonnegative : 0 ≤ e := le_trans (norm_nonneg _) inputError
  apply h.trans
  gcongr

theorem source_ordinary_after_supply1_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryAfterSupply1Int a b ordered)-
      qvalue (sourceOrdinaryAfterSupply1Q a b ordered)‖ ≤
      (2/10^15 : ℝ) := by
  change ‖value (multiply (sourceOrdinarySupplyPulseInt a b ordered)
      (sourceOrdinaryEntranceInt a b ordered))-
    qvalue (qmultiply (ordinaryPointerSupplyQ a b ordered)
      (ordinaryEntranceQ a b ordered))‖ ≤ _
  have h := ordinary_pulse_step_error (sourceOrdinarySupplyPulseInt a b ordered)
    (ordinaryPointerSupplyQ a b ordered) (sourceOrdinaryEntranceInt a b ordered)
    (ordinaryEntranceQ a b ordered) (4/10^16) 6 (ordinary_pulse_int_error _)
    (source_ordinary_supply_pulse_norm a b ordered)
    (source_ordinary_entrance_q_error a b ordered)
    (source_ordinary_entrance_norm a b ordered)
  exact h.trans (by norm_num)

theorem source_ordinary_after_supply2_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryAfterSupply2Int a b ordered)-
      qvalue (sourceOrdinaryAfterSupply2Q a b ordered)‖ ≤
      (9/10^15 : ℝ) := by
  change ‖value (multiply (sourceOrdinarySupplyPulseInt a b ordered)
      (sourceOrdinaryAfterSupply1Int a b ordered))-
    qvalue (qmultiply (ordinaryPointerSupplyQ a b ordered)
      (sourceOrdinaryAfterSupply1Q a b ordered))‖ ≤ _
  have h := ordinary_pulse_step_error (sourceOrdinarySupplyPulseInt a b ordered)
    (ordinaryPointerSupplyQ a b ordered) (sourceOrdinaryAfterSupply1Int a b ordered)
    (sourceOrdinaryAfterSupply1Q a b ordered) (2/10^15) 24
    (ordinary_pulse_int_error _) (source_ordinary_supply_pulse_norm a b ordered)
    (source_ordinary_after_supply1_error a b ordered)
    (source_ordinary_after_supply1_norm a b ordered)
  exact h.trans (by norm_num)

theorem source_ordinary_nine_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryNineInt a b ordered)-
      qvalue (ordinaryNineColumnsQ a b ordered)‖ ≤ (4/10^14 : ℝ) := by
  change ‖value (multiply (sourceOrdinaryLoadPulseInt a b ordered)
      (sourceOrdinaryAfterSupply2Int a b ordered))-
    qvalue (qmultiply (ordinaryPointerLoadQ a b ordered)
      (sourceOrdinaryAfterSupply2Q a b ordered))‖ ≤ _
  have h := ordinary_pulse_step_error (sourceOrdinaryLoadPulseInt a b ordered)
    (ordinaryPointerLoadQ a b ordered) (sourceOrdinaryAfterSupply2Int a b ordered)
    (sourceOrdinaryAfterSupply2Q a b ordered) (9/10^15) 96
    (ordinary_pulse_int_error _) (source_ordinary_load_pulse_norm a b ordered)
    (source_ordinary_after_supply2_error a b ordered)
    (source_ordinary_after_supply2_norm a b ordered)
  exact h.trans (by norm_num)

theorem source_ordinary_after_weak_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryAfterWeakInt a b ordered)-
      qvalue (sourceOrdinaryAfterWeakQ a b ordered)‖ ≤ (2/10^13 : ℝ) := by
  change ‖value (multiply (sourceOrdinaryWeakPulseInt a b ordered)
      (sourceOrdinaryNineInt a b ordered))-
    qvalue (qmultiply (ordinaryPointerWeakQ a b ordered)
      (ordinaryNineColumnsQ a b ordered))‖ ≤ _
  have h := ordinary_pulse_step_error (sourceOrdinaryWeakPulseInt a b ordered)
    (ordinaryPointerWeakQ a b ordered) (sourceOrdinaryNineInt a b ordered)
    (ordinaryNineColumnsQ a b ordered) (4/10^14) 384
    (ordinary_pulse_int_error _) (source_ordinary_weak_pulse_norm a b ordered)
    (source_ordinary_nine_error a b ordered)
    (source_ordinary_nine_norm a b ordered)
  exact h.trans (by norm_num)

theorem source_ordinary_eleven_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryElevenInt a b ordered)-
      qvalue (ordinaryElevenColumnsQ a b ordered)‖ ≤ (1/10^12 : ℝ) := by
  change ‖value (multiply (sourceOrdinaryLoadPulseInt a b ordered)
      (sourceOrdinaryAfterWeakInt a b ordered))-
    qvalue (qmultiply (ordinaryPointerLoadQ a b ordered)
      (sourceOrdinaryAfterWeakQ a b ordered))‖ ≤ _
  have h := ordinary_pulse_step_error (sourceOrdinaryLoadPulseInt a b ordered)
    (ordinaryPointerLoadQ a b ordered) (sourceOrdinaryAfterWeakInt a b ordered)
    (sourceOrdinaryAfterWeakQ a b ordered) (2/10^13) 1536
    (ordinary_pulse_int_error _) (source_ordinary_load_pulse_norm a b ordered)
    (source_ordinary_after_weak_error a b ordered)
    (source_ordinary_after_weak_norm a b ordered)
  exact h.trans (by norm_num)

theorem source_ordinary_arms_actual (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryNineInt a b ordered)-
      nineColumns (s(a,b)) (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
        (ordinaryFullEquiv a b ordered.ne) ordinaryInjection‖ ≤
        (4/10^14 : ℝ) ∧
    ‖value (sourceOrdinaryElevenInt a b ordered)-
      elevenColumns (s(a,b)) (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
        (ordinaryFullEquiv a b ordered.ne) ordinaryInjection‖ ≤
        (1/10^12 : ℝ) := by
  constructor
  · rw [← ordinary_nine_columns_value]
    exact source_ordinary_nine_error a b ordered
  · rw [← ordinary_eleven_columns_value]
    exact source_ordinary_eleven_error a b ordered

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
