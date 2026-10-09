import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformGainQuadratic
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

private theorem ordinary_arm_norm (a b : Basis) (ordered : a < b)
    (V : MatrixQ (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2))
    (hV : ‖qvalue V‖ ≤ (24 : ℝ)) :
    ‖((qvalue V)ᴴ * qvalue (ordinaryPCPointerQ a b)) * qvalue V‖ ≤
      (51264 : ℝ) := by
  have hAdj : ‖(qvalue V)ᴴ‖ ≤ (24 : ℝ) := by
    simpa only [Matrix.l2_opNorm_conjTranspose] using hV
  have hWeighted : ‖(qvalue V)ᴴ * qvalue (ordinaryPCPointerQ a b)‖ ≤
      (2136 : ℝ) :=
    (Matrix.l2_opNorm_mul _ _).trans
      ((mul_le_mul hAdj (source_ordinary_pc_norm a b ordered)
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 24)).trans (by norm_num))
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul hWeighted hV (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 2136)).trans (by norm_num))

theorem source_ordinary_qnet_norm (a b : Basis) (ordered : a < b) :
    ‖sourceOrdinaryQNet a b ordered‖ ≤ (102528 : ℝ) := by
  rw [sourceOrdinaryQNet]
  have h := source_ordinary_selected_norms_24 a b ordered
  exact (norm_sub_le _ _).trans
    ((add_le_add
      (ordinary_arm_norm a b ordered _ h.2)
      (ordinary_arm_norm a b ordered _ h.1)).trans (by norm_num))

theorem source_ordinary_energy_product_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryEnergyProductInt a b ordered)-
      sourceOrdinaryQNet a b ordered *
        qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)‖ ≤
      (7/10^8 : ℝ) := by
  have paid := rectangular_int_mul_error
    (sourceOrdinaryNetInt a b ordered) (sourceOrdinaryBodyInt a b)
    (sourceOrdinaryQNet a b ordered)
    (qvalue (qkron (ordinaryPairBlockQ a b) environmentQ))
    (by norm_num) (by norm_num) (6/10^9) (64/10^30)
    (source_ordinary_net_error a b ordered) (source_ordinary_body_int_error a b)
  rw [sourceOrdinaryEnergyProductInt]
  apply paid.trans
  calc
    (64/10^30 : ℝ)+(6/10^9)*
        (‖qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)‖+64/10^30)+
        ‖sourceOrdinaryQNet a b ordered‖*(64/10^30) ≤
      (64/10^30 : ℝ)+(6/10^9)*(10+64/10^30)+102528*(64/10^30) := by
        gcongr
        · exact source_ordinary_body_norm_10 a b ordered
        · exact source_ordinary_qnet_norm a b ordered
    _ ≤ 7/10^8 := by norm_num

private theorem ordinary_int_trace_value
    (A : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2)) :
    (value A).trace.re =
      ((∑ i : Fin 2 × Fin 2, A.re i i : Int) : ℝ)/(scale : ℝ) := by
  have entry (i : Fin 2 × Fin 2) :
      (value A i i).re = (A.re i i : ℝ)/(scale : ℝ) := by
    simp [value,raw,Complex.mul_re,Complex.inv_re,Complex.inv_im,scale]
    ring
  simp only [Matrix.trace,Matrix.diag,Complex.re_sum]
  simp_rw [entry]
  rw [← Finset.sum_div]
  norm_cast

theorem source_ordinary_gain_cast (a b : Basis) (ordered : a < b) :
    (sourceOrdinaryGainIntQ a b ordered : ℝ)=
      (value (sourceOrdinaryEnergyProductInt a b ordered)).trace.re := by
  rw [sourceOrdinaryGainIntQ,sourceOrdinaryGainNumeratorInt,
    ordinary_int_trace_value]
  norm_cast

theorem source_ordinary_q_gain_cast (a b : Basis) (ordered : a < b) :
    (ordinaryFastGainQ a b ordered : ℝ)=
      Collision.energy (sourceOrdinaryQNet a b ordered)
        (qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)) := by
  rw [ordinaryFastGainQ,Spec.energyQ_value]
  simp only [qvalue_sub,qvalue_multiply,qvalue_adjoint,qvalue_submatrix,
    qvalue_kron,sourceOrdinaryQNet]

theorem source_ordinary_integer_gain_error (a b : Basis) (ordered : a < b) :
    |(sourceOrdinaryGainIntQ a b ordered : ℝ)-
      (smallGainQ (s(a,b)) : ℝ)| ≤ (3/10^7 : ℝ) := by
  rw [← ordinary_fast_gain_original a b ordered,source_ordinary_gain_cast,
    source_ordinary_q_gain_cast,Collision.energy]
  have same : (value (sourceOrdinaryEnergyProductInt a b ordered)).trace.re-
      (sourceOrdinaryQNet a b ordered *
        qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)).trace.re =
      ((value (sourceOrdinaryEnergyProductInt a b ordered)-
        sourceOrdinaryQNet a b ordered *
          qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)).trace).re := by
    simp only [Matrix.trace_sub,Complex.sub_re]
  rw [same]
  calc
    _ ≤ ‖(value (sourceOrdinaryEnergyProductInt a b ordered)-
      sourceOrdinaryQNet a b ordered *
        qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)).trace‖ :=
      Complex.abs_re_le_norm _
    _ ≤ (4 : ℝ)*‖value (sourceOrdinaryEnergyProductInt a b ordered)-
      sourceOrdinaryQNet a b ordered *
        qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)‖ := by
      have h := Donor.trace_norm_bound (value
        (sourceOrdinaryEnergyProductInt a b ordered)-
        sourceOrdinaryQNet a b ordered *
          qvalue (qkron (ordinaryPairBlockQ a b) environmentQ))
      norm_num at h
      simpa only [Matrix.trace_sub] using h
    _ ≤ 4*(7/10^8 : ℝ) :=
      mul_le_mul_of_nonneg_left (source_ordinary_energy_product_error a b ordered)
        (by norm_num)
    _ ≤ 3/10^7 := by norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
