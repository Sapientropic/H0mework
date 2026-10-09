import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteDiagonal.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.SourcePartition
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.OriginalEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.OriginalEnergy
set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Powered.Dynamics
open scoped BigOperators
noncomputable section

/-! Exact original gain partition, using canonical unordered addresses throughout. -/

abbrev HeadNear := {p : HeadOrdinary // nearCond p.val.1 p.val.2}
abbrev HeadMid := {p : HeadOrdinary // midCond p.val.1 p.val.2}
abbrev HeadRest := {p : HeadOrdinary //
  ¬nearCond p.val.1 p.val.2 ∧ ¬midCond p.val.1 p.val.2}

private def nearHeadEmbedding (k : Fin 9) : HeadNear :=
  ⟨⟨(nearA k,nearB k),⟨by fin_cases k <;> decide,near_ordered k⟩⟩,
    by fin_cases k <;> decide⟩

private theorem near_head_embedding_bijective : Function.Bijective nearHeadEmbedding := by
  decide +kernel

private def midHeadEmbedding (k : Fin 2 × Fin 18) : HeadMid :=
  ⟨⟨(midAnchor k.1,midPartner k.2),⟨by
      have h := k.1.isLt
      change k.1.val < 6
      omega,mid_address_ordered k.1 k.2⟩⟩,mid_address_sector k.1 k.2⟩

private theorem mid_head_embedding_bijective : Function.Bijective midHeadEmbedding := by
  decide +kernel

theorem near_original_head_sum :
    nearOriginalGain = ∑ p : HeadNear, (smallGainQ (s(p.val.val.1,p.val.val.2)) : ℝ) := by
  exact Fintype.sum_bijective nearHeadEmbedding near_head_embedding_bijective _ _ (fun _ => rfl)

theorem mid_original_head_sum :
    midOriginalGain = ∑ p : HeadMid, (smallGainQ (s(p.val.val.1,p.val.val.2)) : ℝ) := by
  have h := Fintype.sum_bijective midHeadEmbedding mid_head_embedding_bijective
    (fun k => (smallGainQ (s(midAnchor k.1,midPartner k.2)) : ℝ))
    (fun p => (smallGainQ (s(p.val.val.1,p.val.val.2)) : ℝ)) (fun _ => rfl)
  simpa only [midOriginalGain,Fintype.sum_prod_type] using h

private theorem near_mid_disjoint (p : HeadOrdinary) :
    ¬ (nearCond p.val.1 p.val.2 ∧ midCond p.val.1 p.val.2) := by
  rcases p with ⟨⟨a,b⟩,⟨ha,hab⟩⟩
  simp only [nearCond,midCond]
  have order : a.val < b.val := hab
  omega

def headRestOriginalGain : ℝ :=
  ∑ p : HeadRest, (smallGainQ (s(p.val.val.1,p.val.val.2)) : ℝ)

theorem head_ordinary_sector_partition :
    headOrdinaryOriginalGain = nearOriginalGain+midOriginalGain+headRestOriginalGain := by
  classical
  rw [near_original_head_sum,mid_original_head_sum,headRestOriginalGain,headOrdinaryOriginalGain]
  have filtered (P : HeadOrdinary → Prop) [DecidablePred P] (f : HeadOrdinary → ℝ) :
      (∑ p : {p : HeadOrdinary // P p}, f p.val) =
        ∑ p : HeadOrdinary, if P p then f p else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  rw [filtered (fun p => nearCond p.val.1 p.val.2)
      (fun p => (smallGainQ (s(p.val.1,p.val.2)) : ℝ)),
    filtered (fun p => midCond p.val.1 p.val.2)
      (fun p => (smallGainQ (s(p.val.1,p.val.2)) : ℝ)),
    filtered (fun p => ¬nearCond p.val.1 p.val.2 ∧ ¬midCond p.val.1 p.val.2)
      (fun p => (smallGainQ (s(p.val.1,p.val.2)) : ℝ)),
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases near : nearCond p.val.1 p.val.2
  · have mid : ¬midCond p.val.1 p.val.2 := fun h => near_mid_disjoint p ⟨near,h⟩
    simp [near,mid]
  · by_cases mid : midCond p.val.1 p.val.2 <;> simp [near,mid]

theorem source_net_sector_partition :
    (Spec.netGain : ℝ) = nearOriginalGain+midOriginalGain+headRestOriginalGain+
      headDiagonalOriginalGain+
      ((∑ k : Sym2 Basis, if tailSector k then smallGainQ k else 0 : ℚ) : ℝ) := by
  rw [source_net_head_tail,← head_original_gain_source,headOriginalGain,
    head_ordinary_sector_partition]

abbrev HeadRestLow := {p : HeadRest // p.val.val.2.val < 24}
abbrev HeadRestFar := {p : HeadRest // ¬p.val.val.2.val < 24}

def headRestLowOriginalGain : ℝ :=
  ∑ p : HeadRestLow, (smallGainQ (s(p.val.val.val.1,p.val.val.val.2)) : ℝ)
def headRestFarOriginalGain : ℝ :=
  ∑ p : HeadRestFar, (smallGainQ (s(p.val.val.val.1,p.val.val.val.2)) : ℝ)

theorem head_rest_low_card : Fintype.card HeadRestLow = 78 := by decide +kernel
theorem head_rest_far_card : Fintype.card HeadRestFar = 444 := by decide +kernel

theorem head_rest_low_bounds (p : HeadRestLow) :
    2 ≤ p.val.val.val.1.val ∧ p.val.val.val.1.val < 6 ∧
    p.val.val.val.1 < p.val.val.val.2 ∧ p.val.val.val.2.val < 24 := by
  rcases p with ⟨⟨⟨⟨a,b⟩,⟨ha,hab⟩⟩,⟨hn,hm⟩⟩,hb⟩
  change 2 ≤ a.val ∧ a.val < 6 ∧ a < b ∧ b.val < 24
  change a.val < 6 at ha
  change b.val < 24 at hb
  change ¬nearCond a b at hn
  change ¬midCond a b at hm
  have order : a.val < b.val := hab
  have ne : a ≠ b := ne_of_lt hab
  refine ⟨?_,ha,hab,hb⟩
  by_contra h
  have al : a.val < 2 := by omega
  by_cases bl : b.val < 6
  · exact hn ⟨ne,Or.inl ⟨al,bl⟩⟩
  · exact hm (Or.inl ⟨al,by omega,hb⟩)

theorem head_rest_partition :
    headRestOriginalGain = headRestLowOriginalGain+headRestFarOriginalGain := by
  exact (Fintype.sum_subtype_add_sum_subtype
    (fun p : HeadRest => p.val.val.2.val < 24)
    (fun p : HeadRest => (smallGainQ (s(p.val.val.1,p.val.val.2)) : ℝ))).symm

theorem source_net_remaining_lower :
    midOriginalGain+headRestLowOriginalGain+headRestFarOriginalGain+(3823/10^9 : ℝ) <
      (Spec.netGain : ℝ) := by
  have source := source_net_sector_partition
  rw [head_rest_partition] at source
  have near := near_original_gain_lower
  have diagonal := head_diagonal_original_lower
  have tail := (abs_lt.mp original_rational_tail_budget).1
  linarith only [source,near,diagonal,tail]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
