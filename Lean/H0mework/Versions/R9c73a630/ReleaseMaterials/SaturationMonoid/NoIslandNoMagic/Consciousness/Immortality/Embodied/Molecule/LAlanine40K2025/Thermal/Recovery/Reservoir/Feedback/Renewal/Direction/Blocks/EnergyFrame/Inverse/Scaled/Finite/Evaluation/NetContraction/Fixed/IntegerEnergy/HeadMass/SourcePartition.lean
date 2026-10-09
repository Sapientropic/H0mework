import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.HeadSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.TailPositive.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SharpComparison

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Powered.Dynamics
open scoped BigOperators
noncomputable section

private theorem head_not_tail (p : HeadSource) :
    ¬tailSector (s(p.val.1,p.val.2)) := by
  rw [tail_sector_iff]
  omega

private def headToNonTail (p : HeadSource) : {k : Sym2 Basis // ¬tailSector k} :=
  ⟨s(p.val.1,p.val.2),head_not_tail p⟩

private theorem headToNonTail_injective : Function.Injective headToNonTail := by
  intro p q h
  apply Subtype.ext
  rcases p with ⟨⟨a,b⟩,⟨ha,hab⟩⟩
  rcases q with ⟨⟨c,d⟩,⟨hc,hcd⟩⟩
  have hv := congrArg Subtype.val h
  change s(a,b) = s(c,d) at hv
  rcases (Sym2.mk_eq_mk_iff (p := (a,b)) (q := (c,d))).mp hv with direct | reverse
  · exact direct
  · have h1 : a = d := (Prod.mk.inj reverse).1
    have h2 : b = c := (Prod.mk.inj reverse).2
    subst d
    subst c
    have ab : a = b := le_antisymm hab hcd
    subst b
    rfl

private theorem headToNonTail_surjective : Function.Surjective headToNonTail := by
  rintro ⟨k,hk⟩
  rcases Sym2.mk_surjective k with ⟨⟨a,b⟩,h⟩
  subst k
  change ¬tailSector (s(a,b)) at hk
  have notBoth : ¬(6 ≤ a.val ∧ 6 ≤ b.val) := by
    exact (tail_sector_iff a b).not.mp hk
  rcases le_total a b with hab | hba
  · have habVal : a.val ≤ b.val := hab
    have ha : a.val < 6 := by omega
    exact ⟨⟨(a,b),⟨ha,hab⟩⟩,rfl⟩
  · have hbaVal : b.val ≤ a.val := hba
    have hb : b.val < 6 := by omega
    refine ⟨⟨(b,a),⟨hb,hba⟩⟩,?_⟩
    apply Subtype.ext
    exact Sym2.eq_swap

private def headNonTailEquiv : HeadSource ≃ {k : Sym2 Basis // ¬tailSector k} :=
  Equiv.ofBijective headToNonTail ⟨headToNonTail_injective,headToNonTail_surjective⟩

private theorem head_non_tail_sum :
    (∑ p : HeadSource, smallGainQ (s(p.val.1,p.val.2))) =
      ∑ k : {k : Sym2 Basis // ¬tailSector k}, smallGainQ k.val := by
  exact Fintype.sum_equiv headNonTailEquiv _ _ (fun _ => rfl)

private theorem tail_subtype_sum :
    (∑ k : {k : Sym2 Basis // tailSector k}, smallGainQ k.val) =
      ∑ k : Sym2 Basis, if tailSector k then smallGainQ k else 0 := by
  classical
  symm
  calc
    _ = ∑ k ∈ Finset.univ.filter tailSector, smallGainQ k := by
      simp [Finset.sum_filter]
    _ = _ := Finset.sum_subtype _ (by simp) _

/-- The source's unordered sector sum is exactly its 573-address head plus
    the already certified complementary tail. -/
theorem source_net_head_tail :
    (Spec.netGain : ℝ) = headSourceOriginalGain +
      ((∑ k : Sym2 Basis, if tailSector k then smallGainQ k else 0 : ℚ) : ℝ) := by
  classical
  have split := Fintype.sum_subtype_add_sum_subtype
    (fun k : Sym2 Basis => tailSector k) (fun k => smallGainQ k)
  have qsplit : Spec.netGain =
      (∑ k : {k : Sym2 Basis // tailSector k}, smallGainQ k.val) +
      (∑ k : {k : Sym2 Basis // ¬tailSector k}, smallGainQ k.val) := by
    rw [net_gain_small_sum]
    convert split.symm using 1
    apply Finset.sum_congr
    · ext k
      simp
    · intro k _
      rfl
  rw [qsplit,← head_non_tail_sum,tail_subtype_sum]
  simp only [Rat.cast_add,Rat.cast_sum]
  rw [headSourceOriginalGain]
  ring

/-- This consumes, but does not produce, the remaining source integer margin. -/
theorem original_positive_of_head_staged_margin
    (paid : (1/10^5 : ℝ) < headStagedGain) :
    0 < Resource.pcEnergyOf (bodyRead Weak.execution.joint) -
      Resource.pcEnergyOf (bodyRead Weak.origin.joint) := by
  have head := head_staged_source_error_lt
  have tail := original_rational_tail_budget
  have physical := Spec.original_rational_net_error_sharp
  rw [source_net_head_tail] at physical
  have hh := (abs_lt.mp head).2
  have ht := (abs_lt.mp tail).1
  have hp := (abs_le.mp physical).1
  have margin : (31/10^8 : ℝ) + (6/10^7 : ℝ) + (80/10^7 : ℝ) <
      (1/10^5 : ℝ) := by norm_num
  let r : ℝ := Resource.pcEnergyOf (bodyRead Weak.execution.joint) -
    Resource.pcEnergyOf (bodyRead Weak.origin.joint)
  let s : ℝ := headStagedGain
  let h : ℝ := headSourceOriginalGain
  let t : ℝ := ((∑ k : Sym2 Basis, if tailSector k then smallGainQ k else 0 : ℚ) : ℝ)
  change (1/10^5 : ℝ) < s at paid
  change s-h < (31/10^8 : ℝ) at hh
  change -(6/10^7 : ℝ) < t at ht
  change -(80/10^7 : ℝ) ≤ r-(h+t) at hp
  change 0 < r
  linarith only [paid,margin,hh,ht,hp]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
