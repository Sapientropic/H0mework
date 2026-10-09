import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.LowMass
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Powered.Dynamics
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section

/-! The finite source census is exactly the remaining low ordinary head. -/

private def lowNatAddress (k : Fin 78) : ℕ × ℕ :=
  if k.val < 21 then (2,k.val+3)
  else if k.val < 41 then (3,k.val-21+4)
  else if k.val < 60 then (4,k.val-41+5)
  else (5,k.val-60+6)

private theorem low_nat_bounds (k : Fin 78) :
    2 ≤ (lowNatAddress k).1 ∧ (lowNatAddress k).1 < 6 ∧
    (lowNatAddress k).1 < (lowNatAddress k).2 ∧ (lowNatAddress k).2 < 24 := by
  have h := k.isLt
  unfold lowNatAddress
  split_ifs <;> dsimp <;> omega

def lowSlot (k : Fin 78) : Basis × Basis :=
  (⟨(lowNatAddress k).1,lt_trans (low_nat_bounds k).2.1 (by decide)⟩,
   ⟨(lowNatAddress k).2,lt_trans (low_nat_bounds k).2.2.2 (by decide)⟩)

theorem low_slot_ordered (k : Fin 78) : (lowSlot k).1 < (lowSlot k).2 :=
  (low_nat_bounds k).2.2.1

def lowCanonicalAddress (k : Fin 78) : HeadRestLow := by
  have aLow : 2 ≤ (lowSlot k).1.val := (low_nat_bounds k).1
  have ordered : (lowSlot k).1.val < (lowSlot k).2.val := (low_nat_bounds k).2.2.1
  refine ⟨⟨⟨lowSlot k,⟨(low_nat_bounds k).2.1,ordered⟩⟩,?_⟩,(low_nat_bounds k).2.2.2⟩
  change ¬nearCond (lowSlot k).1 (lowSlot k).2 ∧ ¬midCond (lowSlot k).1 (lowSlot k).2
  constructor
  · rintro ⟨_,near⟩
    rcases near with near | near <;> omega
  · intro mid
    rcases mid with mid | mid <;> omega

private def lowOffset (a b : ℕ) : ℕ :=
  if a=2 then b-3 else if a=3 then 21+(b-4)
  else if a=4 then 41+(b-5) else 60+(b-6)

private theorem low_offset_bound {a b : ℕ} (partner : b < 24) :
    lowOffset a b < 78 := by
  unfold lowOffset
  split_ifs <;> omega

def lowCanonicalIndex (p : HeadRestLow) : Fin 78 :=
  ⟨lowOffset p.val.val.val.1.val p.val.val.val.2.val,
    low_offset_bound (head_rest_low_bounds p).2.2.2⟩

private theorem low_offset_address (k : Fin 78) :
    lowOffset (lowNatAddress k).1 (lowNatAddress k).2 = k.val := by
  have h := k.isLt
  unfold lowNatAddress
  split_ifs <;> simp [lowOffset] <;> omega

private theorem low_address_offset {a b : ℕ}
    (lo : 2 ≤ a) (hi : a < 6) (ordered : a < b) (partner : b < 24) :
    lowNatAddress ⟨lowOffset a b,low_offset_bound partner⟩ = (a,b) := by
  interval_cases a
  all_goals
    norm_num [lowNatAddress,lowOffset]
    split_ifs <;> simp_all <;> omega

def lowCanonicalEquiv : Fin 78 ≃ HeadRestLow where
  toFun := lowCanonicalAddress
  invFun := lowCanonicalIndex
  left_inv k := by
    apply Fin.ext
    exact low_offset_address k
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have h := low_address_offset (head_rest_low_bounds p).1 (head_rest_low_bounds p).2.1
      (head_rest_low_bounds p).2.2.1 (head_rest_low_bounds p).2.2.2
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst h
    · apply Fin.ext
      exact congrArg Prod.snd h

theorem low_canonical_address_bijective : Function.Bijective lowCanonicalAddress :=
  lowCanonicalEquiv.bijective

theorem low_original_gain_source_sum :
    headRestLowOriginalGain =
      ∑ k : Fin 78, (smallGainQ (s((lowSlot k).1,(lowSlot k).2)) : ℝ) := by
  symm
  exact Fintype.sum_bijective lowCanonicalAddress low_canonical_address_bijective _ _ (fun _ => rfl)

theorem low_staged_gain_source_sum :
    headRestLowStagedGain =
      ∑ k : Fin 78, stagedOrdinaryGainIntQ (lowSlot k).1 (lowSlot k).2
        (low_slot_ordered k) := by
  symm
  exact Fintype.sum_bijective lowCanonicalAddress low_canonical_address_bijective _ _ (fun _ => rfl)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
