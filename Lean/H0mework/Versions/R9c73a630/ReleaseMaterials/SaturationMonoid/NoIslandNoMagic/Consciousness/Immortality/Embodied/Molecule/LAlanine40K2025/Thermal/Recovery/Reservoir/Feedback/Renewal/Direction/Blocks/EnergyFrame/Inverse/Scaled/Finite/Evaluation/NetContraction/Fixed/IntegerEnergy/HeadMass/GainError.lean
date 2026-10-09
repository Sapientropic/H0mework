import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.SourceBlock
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformStagedGain
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem source_ordinary_energy_error_by_mass (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryEnergyProductInt a b ordered)-
      sourceOrdinaryQNet a b ordered *
        qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)‖ ≤
      (64/10^30 : ℝ)+(6/10^9)*
        (2*((computedOrdinaryPairBlock a b).trace.re+2/10^20)+64/10^30)+
        102528*(64/10^30) := by
  have paid := rectangular_int_mul_error
    (sourceOrdinaryNetInt a b ordered) (sourceOrdinaryBodyInt a b)
    (sourceOrdinaryQNet a b ordered)
    (qvalue (qkron (ordinaryPairBlockQ a b) environmentQ))
    (by norm_num) (by norm_num) (6/10^9) (64/10^30)
    (source_ordinary_net_error a b ordered) (source_ordinary_body_int_error a b)
  rw [sourceOrdinaryEnergyProductInt]
  apply paid.trans
  gcongr
  · exact source_ordinary_body_norm_by_mass a b ordered
  · exact source_ordinary_qnet_norm a b ordered

theorem staged_ordinary_gain_error_by_mass (a b : Basis) (ordered : a < b) :
    |(stagedOrdinaryGainIntQ a b ordered : ℝ)-
      (smallGainQ (s(a,b)) : ℝ)| ≤
      (5/10^8 : ℝ)*(computedOrdinaryPairBlock a b).trace.re+1/10^20 := by
  rw [staged_ordinary_gain_same,← ordinary_fast_gain_original a b ordered,
    source_ordinary_gain_cast,source_ordinary_q_gain_cast,Collision.energy]
  have same : (value (sourceOrdinaryEnergyProductInt a b ordered)).trace.re-
      (sourceOrdinaryQNet a b ordered *
        qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)).trace.re =
      ((value (sourceOrdinaryEnergyProductInt a b ordered)-
        sourceOrdinaryQNet a b ordered *
          qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)).trace).re := by
    simp only [Matrix.trace_sub,Complex.sub_re]
  rw [same]
  have massNonneg : (0 : ℝ) ≤ (computedOrdinaryPairBlock a b).trace.re :=
    (norm_nonneg _).trans (positive_norm_le_trace_re _
      (computed_ordinary_pair_positive a b))
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
    _ ≤ 4*((64/10^30 : ℝ)+(6/10^9)*
        (2*((computedOrdinaryPairBlock a b).trace.re+2/10^20)+64/10^30)+
        102528*(64/10^30)) :=
      mul_le_mul_of_nonneg_left (source_ordinary_energy_error_by_mass a b ordered)
        (by norm_num)
    _ ≤ (5/10^8 : ℝ)*(computedOrdinaryPairBlock a b).trace.re+1/10^20 := by
      nlinarith only [massNonneg]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
