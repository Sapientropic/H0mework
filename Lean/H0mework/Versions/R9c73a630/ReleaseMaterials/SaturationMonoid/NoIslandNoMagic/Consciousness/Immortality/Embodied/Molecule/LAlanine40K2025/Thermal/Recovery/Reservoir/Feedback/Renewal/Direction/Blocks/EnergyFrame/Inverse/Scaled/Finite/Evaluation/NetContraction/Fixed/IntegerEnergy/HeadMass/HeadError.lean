import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.FullTrace
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def headOrdinaryStagedGain : ℝ :=
  ∑ p : HeadOrdinary,
    (stagedOrdinaryGainIntQ p.val.1 p.val.2 p.property.2 : ℝ)

def headOrdinaryOriginalGain : ℝ :=
  ∑ p : HeadOrdinary,
    (smallGainQ (s(p.val.1,p.val.2)) : ℝ)

theorem head_ordinary_gain_error_lt :
    |headOrdinaryStagedGain-headOrdinaryOriginalGain| < (3/10^7 : ℝ) := by
  have card : Fintype.card HeadOrdinary ≤ 9604 := by
    have h := Fintype.card_subtype_le
      (fun p : Basis × Basis => p.1.val < 6 ∧ p.1 < p.2)
    simpa only [Fintype.card_prod,Fintype.card_fin] using h
  have cardReal : (Fintype.card HeadOrdinary : ℝ) ≤ 9604 := by
    exact_mod_cast card
  change |(∑ p : HeadOrdinary,
      (stagedOrdinaryGainIntQ p.val.1 p.val.2 p.property.2 : ℝ))-
    (∑ p : HeadOrdinary,(smallGainQ (s(p.val.1,p.val.2)) : ℝ))| < _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p : HeadOrdinary,
        |(stagedOrdinaryGainIntQ p.val.1 p.val.2 p.property.2 : ℝ)-
          (smallGainQ (s(p.val.1,p.val.2)) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : HeadOrdinary,
        ((5/10^8 : ℝ)*(computedOrdinaryPairBlock p.val.1 p.val.2).trace.re+
          1/10^20) := by
        apply Finset.sum_le_sum
        intro p _
        exact staged_ordinary_gain_error_by_mass p.val.1 p.val.2 p.property.2
    _ = (5/10^8 : ℝ)*(∑ p : HeadOrdinary,
        (computedOrdinaryPairBlock p.val.1 p.val.2).trace.re)+
        (Fintype.card HeadOrdinary : ℝ)*(1/10^20) := by
        simp only [Finset.sum_add_distrib,← Finset.mul_sum,
          Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ < (5/10^8 : ℝ)*4+9604*(1/10^20) := by
        have mass := head_ordinary_pair_trace_lt_four
        nlinarith only [mass,cardReal]
    _ < 3/10^7 := by norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
