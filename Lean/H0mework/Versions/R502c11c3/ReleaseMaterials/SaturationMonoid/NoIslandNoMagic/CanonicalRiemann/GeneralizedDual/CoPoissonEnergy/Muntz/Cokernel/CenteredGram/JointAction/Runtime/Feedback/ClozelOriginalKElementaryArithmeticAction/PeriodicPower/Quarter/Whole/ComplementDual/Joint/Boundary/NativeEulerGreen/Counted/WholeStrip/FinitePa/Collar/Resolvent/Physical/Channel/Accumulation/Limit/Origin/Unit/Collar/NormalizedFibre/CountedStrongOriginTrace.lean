import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedStrongInput

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKCoefficientBFiniteAction
open scoped Topology

open private rho_le_half counted_input_even normalized_settled_positive from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedStrongInput
open private outer_is_moment count_below_log_scale from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre
open private moment from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel
open private quarter_positive_price quarter_positive_domain from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Endpoint

local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "N" => fun n : Nat => ((n+2 : Nat) : ℝ)
local notation "phase" => fun c (n : Nat) => ((n+2 : Nat) : ℂ)^(-s₀ c)
local notation "scale" => fun c (n : Nat) => (Real.log (N n) : ℂ)*phase c n
local notation "delta" => fun c (n : Nat) => floorFromResponses c+riemannZeta (s₀ c) • elementarySource c-compensated c (n+2)
local notation "U" => fun c n => (scale c n)⁻¹ • delta c n
local notation "A" => fun c (n : Nat) => Prod.fst (clockCoefficients c (actualClockPair c n))
local notation "B" => fun c (n : Nat) => Prod.snd (clockCoefficients c (actualClockPair c n))
local notation "b" => fun c n => (scale c n)⁻¹*B c n
local notation "weight" => fun c (t : ℝ) => (t : ℂ)^(s₀ c-1)
local notation "R" => fun c => burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)
local notation "Y" => countedNormalizedField
local notation "H" => countedHomogeneousSplit

private theorem counted_actual_origin_trace (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    originalCentreTrace c (U c n) = (scale c n)⁻¹*A c n -
      b c n*(2*(∫ t : ℝ in r₀..q, weight c t*seedRaw c.value t)) := by
  let f := fun t : ℝ => weight c t*U c n t
  have even := counted_input_even c n
  have integralCentre : (∫ t : ℝ in 0..r₀, weight c t*FiniteMobiusResolventFlux.cutoff r₀ (U c n) t) =
      ∫ t : ℝ in 0..r₀, f t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ r₀),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ r₀)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (FiniteMobiusResolventFlux.cutoff_read r₀ (U c n)),
      ae_restrict_mem measurableSet_Ioc] with t atx inside
    change weight c t*FiniteMobiusResolventFlux.cutoff r₀ (U c n) t = weight c t*U c n t
    rw [atx, indicator_of_mem (show t ∈ symmetricInterval r₀ from
      ⟨(by norm_num : (-r₀ : ℝ) ≤ 0).trans inside.1.le, inside.2⟩)]
  have collar : (∫ t : ℝ in r₀..q, f t) = b c n*(∫ t : ℝ in r₀..q, weight c t*seedRaw c.value t) := by
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by norm_num : r₀ ≤ q),
      intervalIntegral.integral_of_le (by norm_num : r₀ ≤ q)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (normalized_settled_positive c n), ae_restrict_mem measurableSet_Ioc]
      with t atx inside
    have positive : 0 < t := (by norm_num : 0 < r₀).trans inside.1
    dsimp only [f]
    rw [atx positive inside.2 ((rho_le_half n).trans_lt inside.1)]
    ring
  have domain := quarter_positive_domain c (U c n)
  have first : IntervalIntegrable f volume 0 r₀ := by
    apply domain.mono_set
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ r₀), uIcc_of_le (by norm_num : (0 : ℝ) ≤ q)]
    exact Icc_subset_Icc_right (by norm_num)
  have second : IntervalIntegrable f volume r₀ q := by
    apply domain.mono_set
    rw [uIcc_of_le (by norm_num : r₀ ≤ q), uIcc_of_le (by norm_num : (0 : ℝ) ≤ q)]
    exact Icc_subset_Icc_left (by norm_num)
  have actualMoment : moment c (U c n) = (scale c n)⁻¹*A c n := by
    rw [map_smul, ← outer_is_moment, smul_eq_mul]
  have whole := (quarter_positive_price c (U c n) even).symm.trans actualMoment
  change 2*(∫ t : ℝ in 0..q, f t) = _ at whole
  rw [← intervalIntegral.integral_add_adjacent_intervals first second, collar] at whole
  rw [original_centre_trace_integral c (U c n) even, integralCentre, ← whole]
  ring

theorem actual_counted_origin_trace_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => originalCentreTrace c (U c n)) atTop (𝓝 (-(1/2 : ℂ))) := by
  have aLimit : Tendsto (fun n : Nat => (scale c n)⁻¹*A c n) atTop (𝓝 (-(1/2 : ℂ))) := by
    have source := (actual_scaled_outer_limit c).const_mul (-(1/2 : ℂ))
    simp only [mul_one] at source
    apply source.congr'
    filter_upwards with n
    change (-(1/2 : ℂ))*((scale c n)⁻¹*(-(2*A c n))) = _
    ring
  have bLimit := (count_below_log_scale c).mul_const (2*(∫ t : ℝ in r₀..q, weight c t*seedRaw c.value t))
  have sum := aLimit.sub bLimit
  simp only [zero_mul, sub_zero] at sum
  exact sum.congr' (Eventually.of_forall fun n => (counted_actual_origin_trace c n).symm)

/-- The actual strong mixed graph retains the weighted source coordinate
that determines the original homogeneous output. -/
theorem actual_counted_strong_origin_graph (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => ((splitAtPhysicalCutoff r₀ (U c n), originalCentreTrace c (U c n)),
      splitAtPhysicalCutoff r₀ (Y c n))) atTop (𝓝 (((0,0), -(1/2 : ℂ)), H c)) := by
  have input := (actual_counted_unweighted_source_limit c).prodMk_nhds (actual_counted_origin_trace_limit c)
  have action := ((originAwareMixedAction c).continuous.tendsto ((0,0), -(1/2 : ℂ))).comp input
  have target : originAwareMixedAction c ((0,0), -(1/2 : ℂ)) = H c := by
    change (outgoingCentre c 0, R c 0) - ((2 : ℂ)*(-(1/2 : ℂ))) • H c = _
    rw [map_zero, map_zero, show (2 : ℂ)*(-(1/2 : ℂ)) = -1 by norm_num,
      neg_one_smul, ← Prod.zero_eq_mk, zero_sub, neg_neg]
  rw [target] at action
  have done := input.prodMk_nhds action
  apply done.congr'
  filter_upwards with n
  change (_, originAwareMixedAction c (splitAtPhysicalCutoff r₀ (U c n), originalCentreTrace c (U c n))) = _
  rw [actual_origin_aware_mixed_action c (U c n) (counted_input_even c n)]
  have acted : R c (U c n) = Y c n := by
    rw [map_smul]
    rfl
  rw [acted]

/-- Forgetting the source trace breaks continuous realization even in the
strong topology of both unweighted components of the actual input. -/
theorem no_continuous_unweighted_counted_action (c : BurnolCompletedMellinCoordinate) :
    ¬ ∃ op : (L¹ × BurnolL2) →L[ℂ] (L¹ × BurnolL2),
      ∀ n : Nat, op (splitAtPhysicalCutoff r₀ (U c n)) = splitAtPhysicalCutoff r₀ (Y c n) := by
  rintro ⟨op, actual⟩
  have input := actual_counted_unweighted_source_limit c
  have output := ((op.continuous.tendsto (0,0)).comp input).congr' (Eventually.of_forall actual)
  have limit := tendsto_nhds_unique (actual_counted_strong_origin_graph c).snd_nhds output
  change H c = op 0 at limit
  rw [map_zero] at limit
  have zero := congrArg distributionOfSplit limit
  rw [map_zero] at zero
  exact counted_homogeneous_ne_zero c zero

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
