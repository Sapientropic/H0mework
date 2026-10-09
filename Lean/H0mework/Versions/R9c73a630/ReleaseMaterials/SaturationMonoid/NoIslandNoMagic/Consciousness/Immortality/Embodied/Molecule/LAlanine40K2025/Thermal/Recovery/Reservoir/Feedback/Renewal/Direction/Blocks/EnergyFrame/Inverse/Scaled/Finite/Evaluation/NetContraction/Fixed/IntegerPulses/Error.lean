import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerPulses.Norm
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

private theorem pulse_int_error (P : MatrixQ (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull)) :
    ‖value (quantize P)-qvalue P‖ ≤ (64/10^30 : ℝ) :=
  quantize_error P (by norm_num [OrdinaryFull]) (by norm_num [OrdinaryFull])

private theorem pulse_step_error (PI : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull))
    (P : MatrixQ (OrdinaryFull ⊕ OrdinaryFull) (OrdinaryFull ⊕ OrdinaryFull))
    (VI : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) LoadPrimitive.NativeIndex)
    (V : MatrixQ (OrdinaryFull ⊕ OrdinaryFull) LoadPrimitive.NativeIndex)
    (e n : ℝ) (pulseError : ‖value PI-qvalue P‖ ≤ (64/10^30 : ℝ))
    (pulseNorm : ‖qvalue P‖ ≤ (4 : ℝ))
    (inputError : ‖value VI-qvalue V‖ ≤ e) (inputNorm : ‖qvalue V‖ ≤ n) :
    ‖value (multiply PI VI)-qvalue (qmultiply P V)‖ ≤
      (64/10^30 : ℝ)+(64/10^30 : ℝ)*(n+e)+4*e := by
  rw [qvalue_multiply]
  have h := rectangular_int_mul_error PI VI (qvalue P) (qvalue V)
    (by norm_num [OrdinaryFull]) (by norm_num [LoadPrimitive.NativeIndex])
    (64/10^30) e pulseError inputError
  have enonnegative : 0 ≤ e := le_trans (norm_nonneg _) inputError
  apply h.trans
  gcongr

theorem source_first_after_supply1_error :
    ‖value sourceFirstAfterSupply1Int-qvalue sourceFirstAfterSupply1Q‖ ≤
      (1/10^10 : ℝ) := by
  change ‖value (multiply sourceFirstSupplyPulseInt sourceFirstEntranceInt)-
    qvalue (qmultiply (ordinaryPointerSupplyQ (0 : Basis) (1 : Basis) (by decide))
      (ordinaryEntranceQ (0 : Basis) (1 : Basis) (by decide)))‖ ≤ _
  have h := pulse_step_error sourceFirstSupplyPulseInt
    (ordinaryPointerSupplyQ (0 : Basis) (1 : Basis) (by decide))
    sourceFirstEntranceInt (ordinaryEntranceQ (0 : Basis) (1 : Basis) (by decide))
    (2/10^11) 16800 (pulse_int_error _) source_first_supply_pulse_norm
    source_first_entrance_q_error source_first_entrance_norm
  exact h.trans (by norm_num)

theorem source_first_after_supply2_error :
    ‖value sourceFirstAfterSupply2Int-qvalue sourceFirstAfterSupply2Q‖ ≤
      (5/10^10 : ℝ) := by
  change ‖value (multiply sourceFirstSupplyPulseInt sourceFirstAfterSupply1Int)-
    qvalue (qmultiply (ordinaryPointerSupplyQ (0 : Basis) (1 : Basis) (by decide))
      sourceFirstAfterSupply1Q)‖ ≤ _
  have h := pulse_step_error sourceFirstSupplyPulseInt
    (ordinaryPointerSupplyQ (0 : Basis) (1 : Basis) (by decide))
    sourceFirstAfterSupply1Int sourceFirstAfterSupply1Q
    (1/10^10) 67200 (pulse_int_error _) source_first_supply_pulse_norm
    source_first_after_supply1_error source_first_after_supply1_norm
  exact h.trans (by norm_num)

theorem source_first_nine_error :
    ‖value sourceFirstNineInt-qvalue sourceFirstNineQ‖ ≤ (3/10^9 : ℝ) := by
  change ‖value (multiply sourceFirstLoadPulseInt sourceFirstAfterSupply2Int)-
    qvalue (qmultiply (ordinaryPointerLoadQ (0 : Basis) (1 : Basis) (by decide))
      sourceFirstAfterSupply2Q)‖ ≤ _
  have h := pulse_step_error sourceFirstLoadPulseInt
    (ordinaryPointerLoadQ (0 : Basis) (1 : Basis) (by decide))
    sourceFirstAfterSupply2Int sourceFirstAfterSupply2Q
    (5/10^10) 268800 (pulse_int_error _) source_first_load_pulse_norm
    source_first_after_supply2_error source_first_after_supply2_norm
  exact h.trans (by norm_num)

theorem source_first_after_weak_error :
    ‖value sourceFirstAfterWeakInt-qvalue sourceFirstAfterWeakQ‖ ≤
      (2/10^8 : ℝ) := by
  change ‖value (multiply sourceFirstWeakPulseInt sourceFirstNineInt)-
    qvalue (qmultiply (ordinaryPointerWeakQ (0 : Basis) (1 : Basis) (by decide))
      sourceFirstNineQ)‖ ≤ _
  have h := pulse_step_error sourceFirstWeakPulseInt
    (ordinaryPointerWeakQ (0 : Basis) (1 : Basis) (by decide))
    sourceFirstNineInt sourceFirstNineQ
    (3/10^9) 1075200 (pulse_int_error _) source_first_weak_pulse_norm
    source_first_nine_error source_first_nine_norm
  exact h.trans (by norm_num)

theorem source_first_eleven_error :
    ‖value sourceFirstElevenInt-qvalue sourceFirstElevenQ‖ ≤
      (1/10^7 : ℝ) := by
  change ‖value (multiply sourceFirstLoadPulseInt sourceFirstAfterWeakInt)-
    qvalue (qmultiply (ordinaryPointerLoadQ (0 : Basis) (1 : Basis) (by decide))
      sourceFirstAfterWeakQ)‖ ≤ _
  have h := pulse_step_error sourceFirstLoadPulseInt
    (ordinaryPointerLoadQ (0 : Basis) (1 : Basis) (by decide))
    sourceFirstAfterWeakInt sourceFirstAfterWeakQ
    (2/10^8) 4300800 (pulse_int_error _) source_first_load_pulse_norm
    source_first_after_weak_error source_first_after_weak_norm
  exact h.trans (by norm_num)


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
