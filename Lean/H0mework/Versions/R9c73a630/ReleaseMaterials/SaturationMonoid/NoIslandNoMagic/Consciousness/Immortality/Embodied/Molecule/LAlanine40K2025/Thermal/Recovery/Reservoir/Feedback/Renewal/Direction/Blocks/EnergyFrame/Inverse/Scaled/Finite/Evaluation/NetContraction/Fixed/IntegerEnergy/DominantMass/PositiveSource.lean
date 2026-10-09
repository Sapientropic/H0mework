import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.DominantMass.SourceLink
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.TailPositive.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Producer.StrictThermal
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

abbrev PairSector (P : Basis × Basis → Prop) := {p : Basis × Basis // P p}

def sourceSectorMassQ (P : Basis × Basis → Prop) [DecidablePred P] : ℚ :=
  ∑ p : Basis × Basis, if P p then (pairQ p p).1 else 0

def computedSectorPair (P : Basis × Basis → Prop) [DecidablePred P] :
    Matrix (PairSector P) (PairSector P) ℂ :=
  Field.computedPair.submatrix Subtype.val Subtype.val

theorem computed_sector_positive (P : Basis × Basis → Prop) [DecidablePred P] :
    (computedSectorPair P).PosSemidef := by
  exact computed_pair_positive.submatrix Subtype.val

theorem computed_sector_mass_nonnegative (P : Basis × Basis → Prop)
    [DecidablePred P] : 0 ≤ (computedSectorPair P).trace.re :=
  (Complex.nonneg_iff.mp (computed_sector_positive P).trace_nonneg).1

private theorem source_sector_sum (P : Basis × Basis → Prop) [DecidablePred P] :
    (sourceSectorMassQ P : ℝ) =
      ∑ p : PairSector P, (InputProducts.pair p.val p.val).re := by
  classical
  have filter_sum (f : Basis × Basis → ℝ) :
      (∑ p : Basis × Basis, if P p then f p else 0) =
        ∑ p : PairSector P, f p.val := by
    calc
      _ = ∑ p ∈ Finset.univ.filter P, f p := by simp [Finset.sum_filter]
      _ = _ := Finset.sum_subtype _ (by simp) _
  have cast_sum : (sourceSectorMassQ P : ℝ) =
      ∑ p : Basis × Basis,
        if P p then ((pairQ p p).1 : ℝ) else 0 := by
    simp only [sourceSectorMassQ,Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : P p <;> simp [h]
  rw [cast_sum]
  rw [filter_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact pair_mass_entry_source p.val.1 p.val.2

theorem source_sector_original_trace (P : Basis × Basis → Prop)
    [DecidablePred P] :
    (sourceSectorMassQ P : ℝ) =
      (InputProducts.pair.submatrix
        (Subtype.val : PairSector P → Basis × Basis) Subtype.val).trace.re := by
  rw [source_sector_sum]
  simp only [Matrix.trace,Matrix.diag,Matrix.submatrix_apply,Complex.re_sum]

private theorem sector_entry_error (p : Basis × Basis) :
    |(Field.computedPair p p).re-(InputProducts.pair p p).re| ≤
      (2/10^20 : ℝ) := by
  have h := (matrix_entry_norm_le (Field.computedPair-InputProducts.pair) p p).trans
    InputProducts.pair_error
  have r := (Complex.abs_re_le_norm ((Field.computedPair-InputProducts.pair) p p)).trans h
  simpa only [Matrix.sub_apply,Complex.sub_re] using r

theorem computed_sector_source_error (P : Basis × Basis → Prop)
    [DecidablePred P] :
    |(computedSectorPair P).trace.re-(sourceSectorMassQ P : ℝ)| <
      (1/10^15 : ℝ) := by
  have card : Fintype.card (PairSector P) ≤ 9604 := by
    have h := Fintype.card_subtype_le P
    simpa only [Fintype.card_prod,Fintype.card_fin] using h
  have cardReal : (Fintype.card (PairSector P) : ℝ) ≤ 9604 := by
    exact_mod_cast card
  rw [source_sector_original_trace]
  simp only [computedSectorPair,Matrix.trace,Matrix.diag,Matrix.submatrix_apply,
    Complex.re_sum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p : PairSector P,
        |(Field.computedPair p.val p.val).re-(InputProducts.pair p.val p.val).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : PairSector P, (2/10^20 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      exact sector_entry_error p.val
    _ = (Fintype.card (PairSector P) : ℝ)*(2/10^20 : ℝ) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ < 1/10^15 := by nlinarith only [cardReal]

def nearComputedMass : ℝ :=
  (computedSectorPair (fun p => nearCond p.1 p.2)).trace.re
def midComputedMass : ℝ :=
  (computedSectorPair (fun p => midCond p.1 p.2)).trace.re
def diag2ComputedMass : ℝ :=
  (computedSectorPair (fun p => diag2Cond p.1 p.2)).trace.re
def restComputedMass : ℝ :=
  (computedSectorPair (fun p => restCond p.1 p.2)).trace.re

theorem near_source_sector : sourceSectorMassQ (fun p => nearCond p.1 p.2) = nearMassQ := by
  simp only [sourceSectorMassQ,nearMassQ,Fintype.sum_prod_type]
theorem mid_source_sector : sourceSectorMassQ (fun p => midCond p.1 p.2) = midMassQ := by
  simp only [sourceSectorMassQ,midMassQ,Fintype.sum_prod_type]
theorem diag2_source_sector : sourceSectorMassQ (fun p => diag2Cond p.1 p.2) = diag2MassQ := by
  simp only [sourceSectorMassQ,diag2MassQ,Fintype.sum_prod_type]
theorem rest_source_sector : sourceSectorMassQ (fun p => restCond p.1 p.2) = restMassQ := by
  simp only [sourceSectorMassQ,restMassQ,Fintype.sum_prod_type]

theorem near_computed_mass_bound : (20762/100000 : ℝ) < nearComputedMass := by
  have err := computed_sector_source_error (fun p => nearCond p.1 p.2)
  rw [near_source_sector] at err
  have source : (20763/100000 : ℝ) < (nearMassQ : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).2 near_mass_lower
  have low := (abs_lt.mp err).1
  change -(1/10^15 : ℝ) < nearComputedMass-(nearMassQ : ℝ) at low
  linarith only [source,low]

theorem mid_computed_mass_bound : (74580/100000 : ℝ) < midComputedMass := by
  have err := computed_sector_source_error (fun p => midCond p.1 p.2)
  rw [mid_source_sector] at err
  have source : (74581/100000 : ℝ) < (midMassQ : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).2 mid_mass_lower
  have low := (abs_lt.mp err).1
  change -(1/10^15 : ℝ) < midComputedMass-(midMassQ : ℝ) at low
  linarith only [source,low]

theorem diag2_computed_mass_bound : (4142/100000 : ℝ) < diag2ComputedMass := by
  have err := computed_sector_source_error (fun p => diag2Cond p.1 p.2)
  rw [diag2_source_sector] at err
  have source : (4143/100000 : ℝ) < (diag2MassQ : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).2 diag2_mass_lower
  have low := (abs_lt.mp err).1
  change -(1/10^15 : ℝ) < diag2ComputedMass-(diag2MassQ : ℝ) at low
  linarith only [source,low]

theorem rest_computed_mass_bound : restComputedMass < (515/100000 : ℝ) := by
  have err := computed_sector_source_error (fun p => restCond p.1 p.2)
  rw [rest_source_sector] at err
  have source : (restMassQ : ℝ) < (514/100000 : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).2 rest_mass_upper
  have high := (abs_lt.mp err).2
  change restComputedMass-(restMassQ : ℝ) < (1/10^15 : ℝ) at high
  linarith only [source,high]

theorem rest_computed_mass_nonnegative : 0 ≤ restComputedMass :=
  computed_sector_mass_nonnegative _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
