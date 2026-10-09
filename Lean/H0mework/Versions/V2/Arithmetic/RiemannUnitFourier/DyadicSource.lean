import H0mework.Versions.V2.Arithmetic.RiemannUnitFourier.Realization
import H0mework.Versions.V2.Arithmetic.RiemannUnitFourier.ActionPhysical

/-! The actual Tate tail at radii one and two generates one compact power shell and its original Fourier response. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem tateTail_read (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positiveRadius : 0 < radius) :
    (burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail coordinate radius positiveRadius) : ℝ → ℂ)
      =ᵐ[volume] fun x => if |x| < radius⁻¹ then
        -((|x| : ℝ) : ℂ) ^ (coordinate.value - 1) else 0 := by
  let source := burnolRadiusNormalizedUnitTail coordinate radius positiveRadius
  let raw := burnolRadiusUnitTailRaw coordinate.value radius
  have represents : (source : ℝ → ℂ) =ᵐ[volume] raw := burnolRadiusUnitTail_coeFn coordinate radius positiveRadius
  have rawMem := (Lp.memLp source).ae_eq represents
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp source) rawMem represents
  filter_upwards [burnolTateReciprocalL2_coeFn source, pulled, volume.ae_ne (0 : ℝ)]
    with x read pull nonzero
  have positive := abs_pos.mpr nonzero
  rw [read, pull]
  unfold burnolTateReciprocalRaw raw burnolRadiusUnitTailRaw
  rw [abs_inv]
  have condition : radius < |x|⁻¹ ↔ |x| < radius⁻¹ := by
    simpa only [inv_inv] using (inv_lt_inv₀ (inv_pos.mpr positiveRadius) positive)
  simp only [condition]
  split_ifs
  · rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (abs_nonneg x),
      Complex.cpow_neg, inv_inv, mul_neg]
    congr 1
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero))]
    congr 1
    ring
  · exact mul_zero _

def burnolUnitDyadicTateShell (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail coordinate 2 (by norm_num)) -
    burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail coordinate 1 (by norm_num))

def burnolUnitDyadicTateRaw (s : ℂ) (x : ℝ) : ℂ :=
  if (1 / 2 : ℝ) < |x| ∧ |x| ≤ 1 then ((|x| : ℝ) : ℂ) ^ (s - 1) else 0

theorem burnolUnitDyadicTateShell_coeFn (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolUnitDyadicTateShell coordinate : ℝ → ℂ) =ᵐ[volume] burnolUnitDyadicTateRaw coordinate.value := by
  filter_upwards [Lp.coeFn_sub
    (burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail coordinate 2 (by norm_num)))
    (burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail coordinate 1 (by norm_num))),
    tateTail_read coordinate 2 (by norm_num), tateTail_read coordinate 1 (by norm_num),
    volume.ae_ne (1 / 2 : ℝ), volume.ae_ne (-1 / 2 : ℝ),
    volume.ae_ne (1 : ℝ), volume.ae_ne (-1 : ℝ)] with x subAt leftAt rightAt halfNe negHalfNe oneNe negOneNe
  change (burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail coordinate 2 _) -
    burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail coordinate 1 _) : BurnolL2) x = _
  rw [subAt]
  change burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail coordinate 2 _) x -
    burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail coordinate 1 _) x = _
  rw [leftAt, rightAt]
  have absHalf : |x| ≠ (1 / 2 : ℝ) := by
    intro same
    rcases eq_or_eq_neg_of_abs_eq same with h | h
    · exact halfNe h
    · exact negHalfNe (by linarith)
  have absOne : |x| ≠ (1 : ℝ) := by
    intro same
    rcases eq_or_eq_neg_of_abs_eq same with h | h <;> contradiction
  unfold burnolUnitDyadicTateRaw
  norm_num only [inv_one]
  split_ifs <;> try simp
  all_goals grind

theorem burnolUnitDyadicTateShell_realizes (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolUnitDyadicTateShell coordinate) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (fourierL2 (burnolUnitTailResponse coordinate 2 - burnolUnitTailResponse coordinate 1))) test := by
  unfold burnolUnitDyadicTateShell
  rw [← burnolRemainderSourceReadCLM_apply, map_sub, burnolRemainderSourceReadCLM_apply,
    burnolRemainderSourceReadCLM_apply,
    burnolRemainderRealization_fourier _ _ (burnolUnitTailResponse_realizes coordinate 2 (by norm_num) (by norm_num)),
    burnolRemainderRealization_fourier _ _ (burnolUnitTailResponse_realizes coordinate 1 (by norm_num) (by norm_num))]
  simp only [map_sub, sub_apply]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
