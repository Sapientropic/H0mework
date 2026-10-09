import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.HeadComplete
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

abbrev HeadSource := {p : Basis × Basis // p.1.val < 6 ∧ p.1 ≤ p.2}

private def headOrdinaryEquiv :
    {p : HeadSource // p.val.1 < p.val.2} ≃ HeadOrdinary where
  toFun p := ⟨p.val.val,⟨p.val.property.1,p.property⟩⟩
  invFun p := ⟨⟨p.val,⟨p.property.1,le_of_lt p.property.2⟩⟩,p.property.2⟩
  left_inv p := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl

private def headDiagonalEquiv :
    {p : HeadSource // ¬p.val.1 < p.val.2} ≃ HeadDiagonal where
  toFun p := ⟨p.val.val.1,p.val.property.1⟩
  invFun a := ⟨⟨(a.val,a.val),⟨a.property,le_rfl⟩⟩,by simp⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    have same : p.val.val.1=p.val.val.2 :=
      le_antisymm p.val.property.2 (le_of_not_gt p.property)
    exact Prod.ext rfl same
  right_inv a := by apply Subtype.ext; rfl

def headSourceOriginalGain : ℝ :=
  ∑ p : HeadSource, (smallGainQ (s(p.val.1,p.val.2)) : ℝ)

theorem head_original_gain_source : headOriginalGain=headSourceOriginalGain := by
  classical
  have split := Fintype.sum_subtype_add_sum_subtype
    (fun p : HeadSource => p.val.1 < p.val.2)
    (fun p : HeadSource => (smallGainQ (s(p.val.1,p.val.2)) : ℝ))
  have ordinary :
      (∑ p : {p : HeadSource // p.val.1 < p.val.2},
        (smallGainQ (s(p.val.val.1,p.val.val.2)) : ℝ)) =
        headOrdinaryOriginalGain := by
    rw [headOrdinaryOriginalGain]
    exact Fintype.sum_equiv headOrdinaryEquiv _ _ (fun _ => rfl)
  have diagonal :
      (∑ p : {p : HeadSource // ¬p.val.1 < p.val.2},
        (smallGainQ (s(p.val.val.1,p.val.val.2)) : ℝ)) =
        headDiagonalOriginalGain := by
    rw [headDiagonalOriginalGain]
    apply Fintype.sum_equiv headDiagonalEquiv
    intro p
    have same : p.val.val.1=p.val.val.2 :=
      le_antisymm p.val.property.2 (le_of_not_gt p.property)
    change (smallGainQ (s(p.val.val.1,p.val.val.2)) : ℝ) =
      (smallGainQ (s(p.val.val.1,p.val.val.1)) : ℝ)
    rw [same]
  rw [headOriginalGain,headSourceOriginalGain]
  rw [← ordinary,← diagonal]
  exact split

theorem head_staged_source_error_lt :
    |headStagedGain-headSourceOriginalGain| < (31/10^8 : ℝ) := by
  rw [← head_original_gain_source]
  exact head_gain_original_error_lt

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
