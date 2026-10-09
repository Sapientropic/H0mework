import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.ReferenceGain
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.PaidFamily

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section



/-! The original mid-sector gain and its complete positive-reference energy share a mass-weighted input budget. -/

theorem mid_computed_mass_upper : midComputedMass < (1001/1000 : ℝ) := by
  have diag (p : Basis × Basis) : (0 : ℝ) ≤ (Field.computedPair p p).re :=
    (Complex.nonneg_iff.mp (computed_pair_positive.diag_nonneg (i := p))).1
  have subset : midComputedMass ≤ Field.computedPair.trace.re := by
    simp only [midComputedMass,computedSectorPair,Matrix.trace,Matrix.diag,
      Matrix.submatrix_apply,Complex.re_sum]
    calc
      _ = ∑ p ∈ Finset.univ.filter (fun p : Basis × Basis => midCond p.1 p.2),
          (Field.computedPair p p).re := by
        symm
        exact Finset.sum_subtype _ (by simp) _
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p _ _ => diag p)
  have collision : |Input.finiteCollisionPair.trace.re-1| ≤ (1/10^5 : ℝ) := by
    have h := (Complex.abs_re_le_norm (Input.finiteCollisionPair.trace-1)).trans
      source_finite_collision_trace_near_one
    simpa only [Complex.sub_re,Complex.one_re] using h
  have finite := (abs_le.mp source_finite_pair_trace_real_error).1
  have field := (abs_le.mp source_field_pair_trace_real_error).2
  have c := (abs_le.mp collision).2
  linarith only [subset,finite,field,c]

def midOriginalGain : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 18, (smallGainQ (s(midAnchor a,midPartner b)) : ℝ)

def midReferenceEnergy : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 18,
    (sourceOrdinaryQNet (midAnchor a) (midPartner b) (mid_address_ordered a b) *
      midSectorBody a b).trace.re

theorem mid_original_reference_error :
    |midOriginalGain-midReferenceEnergy| < (4/10^12 : ℝ) := by
  have point (a : Fin 2) (b : Fin 18) :
      |(smallGainQ (s(midAnchor a,midPartner b)) : ℝ)-
        (sourceOrdinaryQNet (midAnchor a) (midPartner b) (mid_address_ordered a b) *
          midSectorBody a b).trace.re| ≤
        (3/10^12 : ℝ)*(midSectorBody a b).trace.re+(2/10^14 : ℝ) :=
    original_ordinary_gain_reference_error _ _ (mid_address_ordered a b)
  have summed : |midOriginalGain-midReferenceEnergy| ≤
      ∑ a : Fin 2, ∑ b : Fin 18,
        ((3/10^12 : ℝ)*(midSectorBody a b).trace.re+(2/10^14 : ℝ)) := by
    rw [midOriginalGain,midReferenceEnergy,← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro a _
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun b _ => point a b))
  have mass := mid_computed_mass_upper
  have sum_eq : (∑ a : Fin 2, ∑ b : Fin 18,
      ((3/10^12 : ℝ)*(midSectorBody a b).trace.re+(2/10^14 : ℝ))) =
      (3/10^12 : ℝ)*midComputedMass+36*(2/10^14 : ℝ) := by
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum,mid_sector_body_mass_sum]
    ring
  rw [sum_eq] at summed
  linarith only [summed,mass]

theorem mid_paid_original_gain_floor (k : Fin 4) :
    (826/10^8-3/10^12 : ℝ)*(midPaidBody k).trace.re-(2/10^14 : ℝ) ≤
      (smallGainQ (s(midPaidA k,midPaidB k)) : ℝ) :=
  original_ordinary_gain_lower_of_order (midPaidA k) (midPaidB k) (mid_paid_ordered k)
    (826/10^8) (mid_paid_qnet_floor k)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
