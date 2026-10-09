import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.DiagonalWeighted
set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Collision Contraction Evaluate
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem source_diagonal_qnet_source (a : Basis) (different : a ≠ 97) :
    sourceDiagonalQNet a different=
      qvalue (compactSelectedNetQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
        (diagonalFullEquiv a different) diagonalInjection diagonalChargedSelect) := by
  simp only [sourceDiagonalQNet,compactSelectedNetQ,qvalue_sub,qvalue_multiply,
    qvalue_adjoint,sourceDiagonalNineSelectedQ,sourceDiagonalElevenSelectedQ]

theorem source_diagonal_net_error (a : Basis) (different : a ≠ 97) :
    ‖value (sourceDiagonalNetInt a different)-sourceDiagonalQNet a different‖ ≤
      (7/10^18 : ℝ) := by
  rw [sourceDiagonalNetInt,value_sub,sourceDiagonalQNet]
  have split (A B C D : Matrix (Fin 2) (Fin 2) ℂ) :
      (A-B)-(C-D)=(A-C)-(B-D) := by abel
  rw [split]
  have errors := source_diagonal_quadratic_errors a different
  exact (norm_sub_le _ _).trans
    ((add_le_add errors.2 errors.1).trans (by norm_num))

private theorem diagonal_arm_norm (a : Basis) (different : a ≠ 97)
    (V : MatrixQ (DiagonalFull ⊕ DiagonalFull) (Fin 2))
    (n : ℝ) (vNorm : ‖qvalue V‖ ≤ n) :
    ‖((qvalue V)ᴴ * qvalue (coordinatePCQ (s(a,a))
      (diagonalFullEquiv a different))) * qvalue V‖ ≤ 89*n*n := by
  have adjNorm : ‖(qvalue V)ᴴ‖ ≤ n := by
    simpa only [Matrix.l2_opNorm_conjTranspose] using vNorm
  have weighted : ‖(qvalue V)ᴴ * qvalue
      (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))‖ ≤ n*89 := by
    exact (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul adjNorm (source_diagonal_pc_norm a different)
        (norm_nonneg _) (le_trans (norm_nonneg _) vNorm))
  have nNonneg : 0 ≤ n := le_trans (norm_nonneg _) vNorm
  calc
    _ ≤ ‖(qvalue V)ᴴ * qvalue
          (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))‖ *
        ‖qvalue V‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (n*89)*n := mul_le_mul weighted vNorm
      (norm_nonneg _) (by positivity)
    _ = 89*n*n := by ring

theorem source_diagonal_qnet_norm (a : Basis) (different : a ≠ 97) :
    ‖sourceDiagonalQNet a different‖ ≤ (4*10^9 : ℝ) := by
  rw [sourceDiagonalQNet]
  have h := source_diagonal_selected_norms a different
  have hn := diagonal_arm_norm a different _ 384 h.1
  have he := diagonal_arm_norm a different _ 6144 h.2
  exact (norm_sub_le _ _).trans
    ((add_le_add he hn).trans (by norm_num))

theorem source_diagonal_energy_product_error (a : Basis) (different : a ≠ 97) :
    ‖value (sourceDiagonalEnergyProductInt a different)-
      sourceDiagonalQNet a different *
        qvalue (qscale (pairQ (a,a) (a,a)) environmentQ)‖ ≤
      (2/10^16 : ℝ) := by
  have paid := rectangular_int_mul_error
    (sourceDiagonalNetInt a different) (sourceDiagonalBodyInt a)
    (sourceDiagonalQNet a different)
    (qvalue (qscale (pairQ (a,a) (a,a)) environmentQ))
    (by norm_num) (by norm_num) (7/10^18) (64/10^30)
    (source_diagonal_net_error a different) (source_diagonal_body_int_error a)
  rw [sourceDiagonalEnergyProductInt]
  apply paid.trans
  calc
    (64/10^30 : ℝ)+(7/10^18)*
        (‖qvalue (qscale (pairQ (a,a) (a,a)) environmentQ)‖+64/10^30)+
        ‖sourceDiagonalQNet a different‖*(64/10^30) ≤
      (64/10^30 : ℝ)+(7/10^18)*(10+64/10^30)+
        (4*10^9)*(64/10^30) := by
      gcongr
      · exact source_diagonal_body_norm a
      · exact source_diagonal_qnet_norm a different
    _ ≤ 2/10^16 := by norm_num

private theorem diagonal_int_trace_value (A : MatrixInt (Fin 2) (Fin 2)) :
    (value A).trace.re =
      ((∑ i : Fin 2, A.re i i : Int) : ℝ)/(scale : ℝ) := by
  have entry (i : Fin 2) :
      (value A i i).re = (A.re i i : ℝ)/(scale : ℝ) := by
    simp [value,raw,Complex.mul_re,Complex.inv_re,Complex.inv_im,scale]
    ring
  simp only [Matrix.trace,Matrix.diag,Complex.re_sum]
  simp_rw [entry]
  rw [← Finset.sum_div]
  norm_cast

theorem source_diagonal_gain_cast (a : Basis) (different : a ≠ 97) :
    (sourceDiagonalGainIntQ a different : ℝ)=
      (value (sourceDiagonalEnergyProductInt a different)).trace.re := by
  rw [sourceDiagonalGainIntQ,sourceDiagonalGainNumeratorInt,
    diagonal_int_trace_value]
  norm_cast

theorem source_diagonal_q_gain_cast (a : Basis) (different : a ≠ 97) :
    (diagonalCompactGainQ a different : ℝ)=
      Collision.energy (sourceDiagonalQNet a different)
        (qvalue (qscale (pairQ (a,a) (a,a)) environmentQ)) := by
  rw [diagonalCompactGainQ,Spec.energyQ_value,source_diagonal_qnet_source]
  rfl

theorem source_diagonal_gain_original_error (a : Basis) (different : a ≠ 97) :
    |(sourceDiagonalGainIntQ a different : ℝ)-
      (smallGainQ (s(a,a)) : ℝ)| ≤ (1/10^15 : ℝ) := by
  rw [← diagonal_compact_gain_original a different,source_diagonal_gain_cast,
    source_diagonal_q_gain_cast,Collision.energy]
  have same : (value (sourceDiagonalEnergyProductInt a different)).trace.re-
      (sourceDiagonalQNet a different *
        qvalue (qscale (pairQ (a,a) (a,a)) environmentQ)).trace.re =
      ((value (sourceDiagonalEnergyProductInt a different)-
        sourceDiagonalQNet a different *
          qvalue (qscale (pairQ (a,a) (a,a)) environmentQ)).trace).re := by
    simp only [Matrix.trace_sub,Complex.sub_re]
  rw [same]
  calc
    _ ≤ ‖(value (sourceDiagonalEnergyProductInt a different)-
      sourceDiagonalQNet a different *
        qvalue (qscale (pairQ (a,a) (a,a)) environmentQ)).trace‖ :=
      Complex.abs_re_le_norm _
    _ ≤ (2 : ℝ)*‖value (sourceDiagonalEnergyProductInt a different)-
      sourceDiagonalQNet a different *
        qvalue (qscale (pairQ (a,a) (a,a)) environmentQ)‖ := by
      have h := Donor.trace_norm_bound (value
        (sourceDiagonalEnergyProductInt a different)-
          sourceDiagonalQNet a different *
            qvalue (qscale (pairQ (a,a) (a,a)) environmentQ))
      have card : Fintype.card (Fin 2)=2 := by decide
      rw [card] at h
      norm_num at h
      simpa only [Matrix.trace_sub] using h
    _ ≤ 2*(2/10^16 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (source_diagonal_energy_product_error a different) (by norm_num)
    _ ≤ 1/10^15 := by norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
