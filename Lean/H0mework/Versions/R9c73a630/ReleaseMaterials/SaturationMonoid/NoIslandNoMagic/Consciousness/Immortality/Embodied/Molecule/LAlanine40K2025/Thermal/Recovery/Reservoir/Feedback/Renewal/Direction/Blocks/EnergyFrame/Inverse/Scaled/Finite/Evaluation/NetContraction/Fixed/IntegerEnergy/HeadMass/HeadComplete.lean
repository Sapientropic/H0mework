import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.DiagonalEnergy
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

abbrev HeadDiagonal := {a : Basis // a.val < 6}

theorem head_diagonal_not_donor (a : HeadDiagonal) : a.val ≠ 97 := by
  intro h
  have bound := a.property
  simp only [h] at bound
  norm_num at bound

def headDiagonalStagedGain : ℝ :=
  ∑ a : HeadDiagonal,
    (sourceDiagonalGainIntQ a.val (head_diagonal_not_donor a) : ℝ)

def headDiagonalOriginalGain : ℝ :=
  ∑ a : HeadDiagonal, (smallGainQ (s(a.val,a.val)) : ℝ)

theorem head_diagonal_gain_error_lt :
    |headDiagonalStagedGain-headDiagonalOriginalGain| < (1/10^12 : ℝ) := by
  have card : Fintype.card HeadDiagonal ≤ 98 := by
    have h := Fintype.card_subtype_le (fun a : Basis => a.val < 6)
    simpa only [Fintype.card_fin] using h
  have cardReal : (Fintype.card HeadDiagonal : ℝ) ≤ 98 := by
    exact_mod_cast card
  change |(∑ a : HeadDiagonal,
      (sourceDiagonalGainIntQ a.val (head_diagonal_not_donor a) : ℝ))-
    (∑ a : HeadDiagonal,(smallGainQ (s(a.val,a.val)) : ℝ))| < _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a : HeadDiagonal,
      |(sourceDiagonalGainIntQ a.val (head_diagonal_not_donor a) : ℝ)-
        (smallGainQ (s(a.val,a.val)) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : HeadDiagonal, (1/10^15 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      exact source_diagonal_gain_original_error a.val (head_diagonal_not_donor a)
    _ = (Fintype.card HeadDiagonal : ℝ)*(1/10^15) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ < 1/10^12 := by nlinarith only [cardReal]

def headStagedGain : ℝ := headOrdinaryStagedGain+headDiagonalStagedGain
def headOriginalGain : ℝ := headOrdinaryOriginalGain+headDiagonalOriginalGain

theorem head_gain_original_error_lt :
    |headStagedGain-headOriginalGain| < (31/10^8 : ℝ) := by
  have same : headStagedGain-headOriginalGain=
      (headOrdinaryStagedGain-headOrdinaryOriginalGain)+
      (headDiagonalStagedGain-headDiagonalOriginalGain) := by
    simp only [headStagedGain,headOriginalGain]
    ring
  rw [same]
  calc
    _ ≤ |headOrdinaryStagedGain-headOrdinaryOriginalGain|+
      |headDiagonalStagedGain-headDiagonalOriginalGain| := abs_add_le _ _
    _ < (3/10^7 : ℝ)+(1/10^12 : ℝ) := by
      linarith only [head_ordinary_gain_error_lt,head_diagonal_gain_error_lt]
    _ < 31/10^8 := by norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
