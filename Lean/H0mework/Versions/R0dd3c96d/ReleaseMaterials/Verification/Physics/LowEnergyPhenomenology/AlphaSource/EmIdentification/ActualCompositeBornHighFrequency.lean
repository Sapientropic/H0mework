import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompositeCoulombDressing

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace LowEnergy.GaussComposite.ActualCompositeCoulombDressing

open GaussCoreHilbert GaussUnitaryHistory
open GaussYukawaOperator FullYDynamicResponse
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open GeneralThreeParticleResponse MixedSpectatorCandidate
open ActualCompositeFieldCurrent ActualCompositeGaugeBand GaussCoreLabel NativeHistoryGrade
open Filter
open scoped Topology InnerProductSpace
attribute [local irreducible] embed compositeResponse compositeBase

private theorem composite_correction_eventually_ne_zero
    (F : Index) (dual advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    ∀ᶠ ω in atTop, originalYCorrection F (candidateTest dual (compositeProfile dual))
      advanced μ hμ ω ≠ 0 := by
  let q := candidateTest dual (compositeProfile dual)
  let A := GaussGradedCompression.compression F
  let c := FullYPairedParseval.direction advanced * μ
  have hc : c ≠ 0 := by
    cases advanced <;> simp [c, FullYPairedParseval.direction, hμ.ne']
  have hq : bounded (embed q) ≠ 0 := by
    intro hz
    rw [bounded_core] at hz
    have ha : GaussYukawaCoefficient.action q = 0 :=
      embed_injective (hz.trans (map_zero embed).symm)
    apply actual_candidate_test_Y_nonzero dual (compositeProfile dual) (composite_profile_source dual)
    rw [← radius_action_return, ha, map_zero]
  have hv := ((ContinuousLinearMap.apply ℂ H (embed q)).continuous.tendsto (-1)).comp
    (YukawaResolventDetection.scaled_line_resolvent_tendsto A
      (GaussGradedCompression.compression_selfAdjoint F) c hc)
  have hb := (bounded.continuous.tendsto _).comp hv
  have hlim : Tendsto (fun ω : ℝ => line c ω • bounded (finiteResolvent F (line c ω) (embed q)))
      atTop (𝓝 (-bounded (embed q))) := by
    change Tendsto (fun ω : ℝ => bounded ((line c ω •
      FullYSourceResolventGraphSplice.resolvent A (line c ω)) (embed q))) atTop
      (𝓝 (bounded ((-1 : H →L[ℂ] H) (embed q)))) at hb
    simpa only [A, finiteResolvent, smul_apply, map_smul, neg_apply, one_apply_eq_self, map_neg] using hb
  filter_upwards [hlim.eventually (eventually_ne_nhds (neg_ne_zero.mpr hq))] with ω hω hz
  exact hω (by rw [correction_zero_bounded_resolvent F q (actual_candidate_test_sector dual _)
    advanced μ hμ ω hz, smul_zero])

/-- The actual full-Y composite leg has a strict Born deficit eventually
on each of its fixed nonreal causal frequency lines. -/
theorem composite_bottom_overlap_eventually_lt_one
    (F : Index) (dual advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    ∀ᶠ ω in atTop, compositeBottomOverlap (compositeCausalLeg F dual false advanced μ hμ ω) < 1 := by
  filter_upwards [composite_correction_eventually_ne_zero F dual advanced μ hμ] with ω hω
  let ell := compositeCausalLeg F dual false advanced μ hμ ω
  let u := embed (compositeResponse ell)
  let P := NativeHistoryGrade.projection (3,0)
  have hsub : u - P u ≠ 0 := by
    change embed (compositeResponse ell) - P (embed (compositeResponse ell)) ≠ 0
    rw [show compositeResponse ell = literalResponse F false (candidateTest dual (compositeProfile dual))
      advanced μ hμ ω from composite_causal_owner F dual false advanced μ hμ ω]
    exact hω
  have hp : P (P u) = P u := by
    have h := congrArg (fun T : H →L[ℂ] H => T u)
      (NativeHistoryGrade.projection_product (3,0) (3,0))
    simpa only [P, if_true, mul_apply_eq_comp] using! h
  have ho : inner ℂ (P u) (u - P u) = 0 := by
    calc
      _ = inner ℂ u (P (u - P u)) := NativeHistoryGrade.projection_symmetric (3,0) _ _
      _ = 0 := by rw [map_sub, hp, sub_self, inner_zero_right]
  have hs : ‖u‖ ^ 2 = ‖P u‖ ^ 2 + ‖u - P u‖ ^ 2 := by
    simpa only [add_sub_cancel, pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P u) (u - P u) ho
  have hstrict : ‖P u‖ < ‖u‖ := by
    nlinarith [norm_nonneg u, norm_nonneg (P u), sq_pos_of_pos (norm_pos_iff.mpr hsub)]
  have hbase : embed (compositeBase ell) = P u := by
    rw [← composite_response_bottom ell, embed_project]
  unfold compositeBottomOverlap
  change ‖embed (compositeBase ell)‖ / ‖u‖ < 1
  rw [hbase]
  exact (div_lt_one (lt_of_le_of_lt (norm_nonneg _) hstrict)).mpr hstrict

-- The other three legs keep their independent preparation and frequency.
theorem composite_coulomb_overlap_eventually_lt_one
    (F : Index) (dual advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (dR sL sR : CompositeLeg) :
    ∀ᶠ ω in atTop, compositeCoulombOverlap
      (compositeCausalLeg F dual false advanced μ hμ ω) dR sL sR < 1 := by
  filter_upwards [composite_bottom_overlap_eventually_lt_one F dual advanced μ hμ] with ω hω
  have dr := composite_bottom_overlap_bounds dR
  have sl := composite_bottom_overlap_bounds sL
  have sr := composite_bottom_overlap_bounds sR
  unfold compositeCoulombOverlap
  calc
    _ < 1 * compositeBottomOverlap dR * compositeBottomOverlap sL * compositeBottomOverlap sR :=
      mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hω dr.1) sl.1) sr.1
    _ ≤ 1 := by
      rw [one_mul]
      exact mul_le_one₀ (mul_le_one₀ dr.2 sl.1.le sl.2) sr.1.le sr.2

end LowEnergy.GaussComposite.ActualCompositeCoulombDressing
