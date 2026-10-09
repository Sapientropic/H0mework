import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.SectorPartition
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Powered.Dynamics
open scoped BigOperators
noncomputable section

/-! The high-partner budget uses the exact remaining canonical source addresses. -/

def headFarSourceMassQ : ℚ :=
  ∑ p : HeadRestFar,
    ((pairQ (p.val.val.val.1,p.val.val.val.2) (p.val.val.val.1,p.val.val.val.2)).1+
      (pairQ (p.val.val.val.2,p.val.val.val.1) (p.val.val.val.2,p.val.val.val.1)).1)

theorem head_far_source_mass_upper : headFarSourceMassQ < (15058/10^10 : ℚ) := by
  decide +kernel

def headFarReferenceMass : ℝ :=
  ∑ p : HeadRestFar, (computedOrdinaryBody p.val.val.val.1 p.val.val.val.2).trace.re

private theorem ordinary_mass_source_error (a b : Basis) :
    |(computedOrdinaryBody a b).trace.re-
      (((pairQ (a,b) (a,b)).1+(pairQ (b,a) (b,a)).1 : ℚ) : ℝ)| ≤ (4/10^20 : ℝ) := by
  have e0 := source_pair_entry_error (a,b)
  have e1 := source_pair_entry_error (b,a)
  rw [← pair_mass_entry_source a b] at e0
  rw [← pair_mass_entry_source b a] at e1
  rw [computed_ordinary_body_trace]
  simp only [computedOrdinaryPairBlock,Matrix.trace,Matrix.diag,Matrix.submatrix_apply,
    Fin.sum_univ_two,pairAddress,Complex.add_re,Rat.cast_add]
  change |(Field.computedPair (a,b) (a,b)).re+(Field.computedPair (b,a) (b,a)).re-
    (((pairQ (a,b) (a,b)).1 : ℝ)+((pairQ (b,a) (b,a)).1 : ℝ))| ≤ (4/10^20 : ℝ)
  have balance (x y u v : ℝ) : x+y-(u+v)=(x-u)+(y-v) := by ring
  rw [balance]
  exact (abs_add_le _ _).trans ((add_le_add e0 e1).trans (by norm_num))

theorem head_far_reference_mass_error :
    |headFarReferenceMass-(headFarSourceMassQ : ℝ)| ≤ (1776/10^20 : ℝ) := by
  simp only [headFarReferenceMass,headFarSourceMassQ,Rat.cast_sum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p : HeadRestFar,
        |(computedOrdinaryBody p.val.val.val.1 p.val.val.val.2).trace.re-
          (((pairQ (p.val.val.val.1,p.val.val.val.2) (p.val.val.val.1,p.val.val.val.2)).1+
            (pairQ (p.val.val.val.2,p.val.val.val.1) (p.val.val.val.2,p.val.val.val.1)).1 : ℚ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : HeadRestFar, (4/10^20 : ℝ) :=
      Finset.sum_le_sum (fun p _ => ordinary_mass_source_error _ _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,head_rest_far_card,nsmul_eq_mul]
      norm_num

theorem head_far_reference_mass_upper : headFarReferenceMass < (1506/10^9 : ℝ) := by
  have source : (headFarSourceMassQ : ℝ) < (15058/10^10 : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).2 head_far_source_mass_upper
  have error := (abs_le.mp head_far_reference_mass_error).2
  linarith only [source,error]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
