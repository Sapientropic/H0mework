import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.DominantMass.Total
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped BigOperators

def nearCond (a b : Basis) : Prop :=
  a ≠ b ∧ ((a.val < 2 ∧ b.val < 6) ∨ (b.val < 2 ∧ a.val < 6))
def midCond (a b : Basis) : Prop :=
  (a.val < 2 ∧ 6 ≤ b.val ∧ b.val < 24) ∨
  (b.val < 2 ∧ 6 ≤ a.val ∧ a.val < 24)
def diag2Cond (a b : Basis) : Prop := a = b ∧ a.val < 2
def restCond (a b : Basis) : Prop :=
  ¬nearCond a b ∧ ¬midCond a b ∧ ¬diag2Cond a b

instance nearCondDecidable (a b : Basis) : Decidable (nearCond a b) := by
  unfold nearCond
  infer_instance
instance midCondDecidable (a b : Basis) : Decidable (midCond a b) := by
  unfold midCond
  infer_instance
instance diag2CondDecidable (a b : Basis) : Decidable (diag2Cond a b) := by
  unfold diag2Cond
  infer_instance
instance restCondDecidable (a b : Basis) : Decidable (restCond a b) := by
  unfold restCond
  infer_instance

def nearMassQ : ℚ :=
  ∑ a : Basis, ∑ b : Basis,
    if nearCond a b then (pairQ (a,b) (a,b)).1 else 0
def midMassQ : ℚ :=
  ∑ a : Basis, ∑ b : Basis,
    if midCond a b then (pairQ (a,b) (a,b)).1 else 0
def diag2MassQ : ℚ :=
  ∑ a : Basis, ∑ b : Basis,
    if diag2Cond a b then (pairQ (a,b) (a,b)).1 else 0
def restMassQ : ℚ :=
  ∑ a : Basis, ∑ b : Basis,
    if restCond a b then (pairQ (a,b) (a,b)).1 else 0

theorem near_mass_lower : (20763/100000 : ℚ) < nearMassQ := by decide +kernel
theorem mid_mass_lower : (74581/100000 : ℚ) < midMassQ := by decide +kernel
theorem diag2_mass_lower : (4143/100000 : ℚ) < diag2MassQ := by decide +kernel

private theorem near_mid_disjoint (a b : Basis) :
    nearCond a b → ¬midCond a b := by
  rintro ⟨_, hnear⟩ hmid
  rcases hnear with hnear | hnear <;> rcases hmid with hmid | hmid <;> omega
private theorem near_diag_disjoint (a b : Basis) :
    nearCond a b → ¬diag2Cond a b := by
  rintro ⟨hne,_⟩ ⟨heq,_⟩
  exact hne heq
private theorem mid_diag_disjoint (a b : Basis) :
    midCond a b → ¬diag2Cond a b := by
  intro hmid hdiag
  rcases hdiag with ⟨heq,_⟩
  subst b
  rcases hmid with hmid | hmid <;> omega

private theorem pair_mass_partition_entry (a b : Basis) :
    (pairQ (a,b) (a,b)).1 =
      (if nearCond a b then (pairQ (a,b) (a,b)).1 else 0) +
      (if midCond a b then (pairQ (a,b) (a,b)).1 else 0) +
      (if diag2Cond a b then (pairQ (a,b) (a,b)).1 else 0) +
      (if restCond a b then (pairQ (a,b) (a,b)).1 else 0) := by
  by_cases hn : nearCond a b
  · have hm := near_mid_disjoint a b hn
    have hd := near_diag_disjoint a b hn
    simp [hn,hm,hd,restCond]
  · by_cases hm : midCond a b
    · have hd := mid_diag_disjoint a b hm
      simp [hn,hm,hd,restCond]
    · by_cases hd : diag2Cond a b
      · simp [hn,hm,hd,restCond]
      · simp [hn,hm,hd,restCond]

theorem full_pair_mass_partition :
    fullPairMassQ = nearMassQ+midMassQ+diag2MassQ+restMassQ := by
  have source : fullPairMassQ =
      ∑ a : Basis, ∑ b : Basis, (pairQ (a,b) (a,b)).1 := by
    simp only [fullPairMassQ,totalPairZ,Prod.fst_sum]
  rw [source]
  simp only [nearMassQ,midMassQ,diag2MassQ,restMassQ,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact pair_mass_partition_entry a b

theorem rest_mass_upper : restMassQ < (514/100000 : ℚ) := by
  linarith only [full_pair_mass_partition,full_pair_mass_upper,
    near_mass_lower,mid_mass_lower,diag2_mass_lower]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
