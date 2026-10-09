import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.DiagonalNorm
set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Collision Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_diagonal_entrance_error (a : Basis) (different : a ≠ 97) :
    ‖value (sourceDiagonalEntranceInt a different)-
      qvalue (sourceDiagonalEntranceQ a different)‖ ≤ (1/10^27 : ℝ) := by
  have columns := source_diagonal_columns_actual a different
  rw [← source_columns_value] at columns
  have paid := rectangular_int_mul_error
    (sourceDiagonalColumnsInt a different) (sourceDiagonalReceivedInt a)
    (qvalue (sourceColumnsQ (s(a,a)) (diagonalFullEquiv a different)
      diagonalInjection)) (qvalue (sourceDiagonalReceivedQ a))
    (by norm_num [DiagonalFull]) (by norm_num) (64/10^30) (64/10^30)
    columns (source_diagonal_received_error a)
  change ‖value (multiply (sourceDiagonalColumnsInt a different)
    (sourceDiagonalReceivedInt a))-
    qvalue (qmultiply (sourceColumnsQ (s(a,a)) (diagonalFullEquiv a different)
      diagonalInjection) (sourceDiagonalReceivedQ a))‖ ≤ _
  rw [qvalue_multiply]
  apply paid.trans
  calc
    (64/10^30 : ℝ)+(64/10^30)*
        (‖qvalue (sourceDiagonalReceivedQ a)‖+64/10^30)+
        ‖qvalue (sourceColumnsQ (s(a,a)) (diagonalFullEquiv a different)
          diagonalInjection)‖*(64/10^30) ≤
      (64/10^30 : ℝ)+(64/10^30)*(1001/1000+64/10^30)+
        5*(64/10^30) := by
      gcongr
      · exact source_diagonal_received_norm a
      · exact source_diagonal_columns_norm a different
    _ ≤ 1/10^27 := by norm_num

private theorem diagonal_pulse_int_error
    (P : MatrixQ (DiagonalFull ⊕ DiagonalFull) (DiagonalFull ⊕ DiagonalFull)) :
    ‖value (quantize P)-qvalue P‖ ≤ (64/10^30 : ℝ) :=
  quantize_error P (by norm_num [DiagonalFull]) (by norm_num [DiagonalFull])

private theorem diagonal_pulse_step_error
    (PI : MatrixInt (DiagonalFull ⊕ DiagonalFull)
      (DiagonalFull ⊕ DiagonalFull))
    (P : MatrixQ (DiagonalFull ⊕ DiagonalFull)
      (DiagonalFull ⊕ DiagonalFull))
    (VI : MatrixInt (DiagonalFull ⊕ DiagonalFull) (Fin 2 × Fin 2))
    (V : MatrixQ (DiagonalFull ⊕ DiagonalFull) (Fin 2 × Fin 2))
    (e n : ℝ) (pulseError : ‖value PI-qvalue P‖ ≤ (64/10^30 : ℝ))
    (pulseNorm : ‖qvalue P‖ ≤ (4 : ℝ))
    (inputError : ‖value VI-qvalue V‖ ≤ e)
    (inputNorm : ‖qvalue V‖ ≤ n) :
    ‖value (multiply PI VI)-qvalue (qmultiply P V)‖ ≤
      (64/10^30 : ℝ)+(64/10^30)*(n+e)+4*e := by
  rw [qvalue_multiply]
  have h := rectangular_int_mul_error PI VI (qvalue P) (qvalue V)
    (by norm_num [DiagonalFull]) (by norm_num)
    (64/10^30) e pulseError inputError
  have enonnegative : 0 ≤ e := le_trans (norm_nonneg _) inputError
  apply h.trans
  gcongr

theorem source_diagonal_after_supply1_error (a : Basis) (different : a ≠ 97) :
    ‖value (sourceDiagonalAfterSupply1Int a different)-
      qvalue (sourceDiagonalAfterSupply1Q a different)‖ ≤
      (5/10^27 : ℝ) := by
  change ‖value (multiply (sourceDiagonalSupplyInt a different)
      (sourceDiagonalEntranceInt a different))-
    qvalue (qmultiply (coordinateSupplyQ (s(a,a)) (diagonalFullEquiv a different))
      (sourceDiagonalEntranceQ a different))‖ ≤ _
  have h := diagonal_pulse_step_error (sourceDiagonalSupplyInt a different)
    (coordinateSupplyQ (s(a,a)) (diagonalFullEquiv a different))
    (sourceDiagonalEntranceInt a different) (sourceDiagonalEntranceQ a different)
    (1/10^27) 6 (diagonal_pulse_int_error _)
    (source_diagonal_supply_norm a different)
    (source_diagonal_entrance_error a different)
    (source_diagonal_entrance_norm a different)
  exact h.trans (by norm_num)

theorem source_diagonal_after_supply2_error (a : Basis) (different : a ≠ 97) :
    ‖value (sourceDiagonalAfterSupply2Int a different)-
      qvalue (sourceDiagonalAfterSupply2Q a different)‖ ≤
      (3/10^26 : ℝ) := by
  change ‖value (multiply (sourceDiagonalSupplyInt a different)
      (sourceDiagonalAfterSupply1Int a different))-
    qvalue (qmultiply (coordinateSupplyQ (s(a,a)) (diagonalFullEquiv a different))
      (sourceDiagonalAfterSupply1Q a different))‖ ≤ _
  have h := diagonal_pulse_step_error (sourceDiagonalSupplyInt a different)
    (coordinateSupplyQ (s(a,a)) (diagonalFullEquiv a different))
    (sourceDiagonalAfterSupply1Int a different) (sourceDiagonalAfterSupply1Q a different)
    (5/10^27) 24 (diagonal_pulse_int_error _)
    (source_diagonal_supply_norm a different)
    (source_diagonal_after_supply1_error a different)
    (source_diagonal_after_supply1_norm a different)
  exact h.trans (by norm_num)

theorem source_diagonal_nine_error (a : Basis) (different : a ≠ 97) :
    ‖value (sourceDiagonalNineInt a different)-
      qvalue (nineColumnsQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
        (diagonalFullEquiv a different) diagonalInjection)‖ ≤
      (2/10^25 : ℝ) := by
  change ‖value (multiply (sourceDiagonalLoadInt a different)
      (sourceDiagonalAfterSupply2Int a different))-
    qvalue (qmultiply (coordinateLoadQ (s(a,a)) (diagonalFullEquiv a different))
      (sourceDiagonalAfterSupply2Q a different))‖ ≤ _
  have h := diagonal_pulse_step_error (sourceDiagonalLoadInt a different)
    (coordinateLoadQ (s(a,a)) (diagonalFullEquiv a different))
    (sourceDiagonalAfterSupply2Int a different) (sourceDiagonalAfterSupply2Q a different)
    (3/10^26) 96 (diagonal_pulse_int_error _)
    (source_diagonal_load_norm a different)
    (source_diagonal_after_supply2_error a different)
    (source_diagonal_after_supply2_norm a different)
  exact h.trans (by norm_num)

theorem source_diagonal_after_weak_error (a : Basis) (different : a ≠ 97) :
    ‖value (sourceDiagonalAfterWeakInt a different)-
      qvalue (sourceDiagonalAfterWeakQ a different)‖ ≤
      (1/10^24 : ℝ) := by
  change ‖value (multiply (sourceDiagonalWeakInt a different)
      (sourceDiagonalNineInt a different))-
    qvalue (qmultiply (coordinateWeakQ (s(a,a)) (diagonalFullEquiv a different))
      (nineColumnsQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
        (diagonalFullEquiv a different) diagonalInjection))‖ ≤ _
  have h := diagonal_pulse_step_error (sourceDiagonalWeakInt a different)
    (coordinateWeakQ (s(a,a)) (diagonalFullEquiv a different))
    (sourceDiagonalNineInt a different)
    (nineColumnsQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
      (diagonalFullEquiv a different) diagonalInjection)
    (2/10^25) 384 (diagonal_pulse_int_error _)
    (source_diagonal_weak_norm a different)
    (source_diagonal_nine_error a different)
    (source_diagonal_nine_norm a different)
  exact h.trans (by norm_num)

theorem source_diagonal_eleven_error (a : Basis) (different : a ≠ 97) :
    ‖value (sourceDiagonalElevenInt a different)-
      qvalue (elevenColumnsQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
        (diagonalFullEquiv a different) diagonalInjection)‖ ≤
      (5/10^24 : ℝ) := by
  change ‖value (multiply (sourceDiagonalLoadInt a different)
      (sourceDiagonalAfterWeakInt a different))-
    qvalue (qmultiply (coordinateLoadQ (s(a,a)) (diagonalFullEquiv a different))
      (sourceDiagonalAfterWeakQ a different))‖ ≤ _
  have h := diagonal_pulse_step_error (sourceDiagonalLoadInt a different)
    (coordinateLoadQ (s(a,a)) (diagonalFullEquiv a different))
    (sourceDiagonalAfterWeakInt a different) (sourceDiagonalAfterWeakQ a different)
    (1/10^24) 1536 (diagonal_pulse_int_error _)
    (source_diagonal_load_norm a different)
    (source_diagonal_after_weak_error a different)
    (source_diagonal_after_weak_norm a different)
  exact h.trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
