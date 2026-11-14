import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.OutgoingCentre
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.HomogeneousFibre
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Resolvent

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Resolvent (actual_R_raw prefixRaw)

open private moment from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel
open private quarter_positive_price quarter_positive_domain from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Endpoint
open private cutoff_split_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.HomogeneousFibre
open private centreLimit centre_integrable homogeneous_tail_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.WeakLimit

local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "box" => symmetricInterval r₀
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R" => fun c => burnolDirectRightResolventCLM (barC c)
local notation "Cut" => FiniteMobiusResolventFlux.cutoff r₀
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "weight" => fun c (t : ℝ) => (t : ℂ)^(s₀ c-1)
local notation "power" => fun c (x : ℝ) => ((|x| : ℝ) : ℂ)^(-s₀ c)
local notation "H" => countedHomogeneousSplit

/-- The original weighted source read, restricted to the same compact centre. -/
def originalCentreTrace (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] ℂ := (moment c).comp Cut

private theorem centre_cut_even (v : BurnolL2) (even : reflectL2 v = v) : reflectL2 (Cut v) = Cut v := by
  have restricted := restrictToInterval_reflectL2 r₀ v
  change burnolRadiusRestriction r₀ (reflectL2 v) = reflectRestricted r₀ (burnolRadiusRestriction r₀ v) at restricted
  rw [even] at restricted
  change reflectL2 (burnolRadiusZeroExtension r₀ (burnolRadiusRestriction r₀ v)) = _
  rw [burnolRadiusZeroExtension_reflect, ← restricted]
  rfl

private theorem compact_weighted_before (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (u : ℝ) (nonnegative : 0 ≤ u) (inside : u ≤ q) :
    IntervalIntegrable (fun t : ℝ => weight c t*v t) volume 0 u := by
  apply (quarter_positive_domain c v).mono_set
  rw [uIcc_of_le nonnegative, uIcc_of_le (by norm_num : (0 : ℝ) ≤ q)]
  exact Icc_subset_Icc_right inside

private theorem compact_prefix_after (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (u : ℝ) (outside : r₀ ≤ u) :
    (∫ t : ℝ in 0..u, weight c t*Cut v t) = ∫ t : ℝ in 0..r₀, weight c t*Cut v t := by
  let f := fun t : ℝ => weight c t*Cut v t
  have empty : f =ᵐ[volume.restrict (Ioc r₀ u)] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae (FiniteMobiusResolventFlux.cutoff_read r₀ v),
      ae_restrict_mem measurableSet_Ioc] with t cut member
    have beyond : t ∉ box := fun h => (not_le_of_gt member.1) h.2
    change weight c t*Cut v t = _
    rw [cut, indicator_of_notMem beyond, mul_zero]
  have zeroInt : Integrable (fun _ : ℝ => (0 : ℂ)) (volume.restrict (Ioc r₀ u)) := by simp
  have after : IntervalIntegrable f volume r₀ u :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le outside).mpr (zeroInt.congr empty.symm)
  have before : IntervalIntegrable f volume 0 r₀ := compact_weighted_before c (Cut v) r₀ (by norm_num) (by norm_num)
  rw [← intervalIntegral.integral_add_adjacent_intervals before after,
    intervalIntegral.integral_of_le outside, integral_eq_zero_of_ae empty, add_zero]

theorem original_centre_trace_integral (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (even : reflectL2 v = v) :
    originalCentreTrace c v = 2*(∫ t : ℝ in 0..r₀, weight c t*Cut v t) := by
  change moment c (Cut v) = _
  rw [quarter_positive_price c (Cut v) (centre_cut_even v even), compact_prefix_after c v q (by norm_num)]

private theorem exterior_R_zero_in_centre (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (even : reflectL2 v = v) :
    ∀ᵐ x : ℝ ∂volume, |x| ≤ r₀ → R c (v-Cut v) x = 0 := by
  have exteriorEven : reflectL2 (v-Cut v) = v-Cut v := by rw [map_sub, even, centre_cut_even v even]
  have original := actual_R_raw (barC c) (v-Cut v) _ Filter.EventuallyEq.rfl exteriorEven
  have empty : ∀ᵐ t : ℝ ∂volume, t ∈ box → (v-Cut v : BurnolL2) t = 0 := by
    filter_upwards [Lp.coeFn_sub v (Cut v), FiniteMobiusResolventFlux.cutoff_read r₀ v] with t difference cut member
    rw [difference, Pi.sub_apply, cut, indicator_of_mem member, sub_self]
  filter_upwards [original] with x actual inside
  change R c (v-Cut v) x = _ at actual
  rw [actual, prefixRaw]
  have integralZero : (∫ t : ℝ in 0..|x|, (t : ℂ)^((barC c).value-1)*(v-Cut v : BurnolL2) t) = 0 := by
    rw [intervalIntegral.integral_of_le (abs_nonneg x)]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae empty, ae_restrict_mem measurableSet_Ioc] with t gone range
    have member : t ∈ box := ⟨(by norm_num : (-r₀ : ℝ) ≤ 0).trans range.1.le, range.2.trans inside⟩
    rw [gone member, mul_zero]
    rfl
  rw [integralZero, mul_zero]

/-- The complete mixed original R action reads the unweighted centre,
the actual exterior, and the original weighted trace of that same centre. -/
def originAwareMixedAction (c : BurnolCompletedMellinCoordinate) :
    ((L¹ × BurnolL2) × ℂ) →L[ℂ] (L¹ × BurnolL2) :=
  (((outgoingCentre c).comp (ContinuousLinearMap.fst ℂ L¹ BurnolL2)).prod
    ((R c).comp (ContinuousLinearMap.snd ℂ L¹ BurnolL2))).comp
      (ContinuousLinearMap.fst ℂ (L¹ × BurnolL2) ℂ) -
    ((2 : ℂ) • ContinuousLinearMap.snd ℂ (L¹ × BurnolL2) ℂ).smulRight (H c)

/-- The source trace is consumed before forming either output component. -/
theorem actual_origin_aware_mixed_action (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (even : reflectL2 v = v) :
    originAwareMixedAction c (splitAtPhysicalCutoff r₀ v, originalCentreTrace c v) =
      splitAtPhysicalCutoff r₀ (R c v) := by
  let cut := Cut v
  let ext : BurnolL2 := v-cut
  let w := R c cut
  let h := R c ext
  let core := (splitAtPhysicalCutoff r₀ v).1
  let out := outgoingCentre c core
  let a := originalCentreTrace c v
  let scaled := (2*a) • H c
  have centreRead := (originalPhysicalCutoff_integrable r₀ v).coeFn_toL1
  have trace : a = 2*(∫ t : ℝ in 0..r₀, weight c t*cut t) := original_centre_trace_integral c v even
  have compact := actual_R_raw (barC c) cut _ Filter.EventuallyEq.rfl (centre_cut_even v even)
  have extent := exterior_R_zero_in_centre c v even
  have full : R c v = w+h := by
    change R c v = R c cut+R c (v-cut)
    rw [map_sub]
    abel
  have whole : ∀ᵐ x : ℝ ∂volume, R c v x = w x+h x := by
    rw [full]
    exact Lp.coeFn_add w h
  have outward (x : ℝ) : (∫ t in Ioc |x| r₀, weight c t*core t) =
      ∫ t in Ioc |x| r₀, weight c t*cut t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae centreRead] with t atx
    change core t = cut t at atx
    rw [atx]
  have inner : ∀ᵐ x : ℝ ∂volume, |x| ≤ r₀ → w x = out x - a*power c x := by
    filter_upwards [compact, outgoing_centre_read c core] with x read outwardRead inside
    change w x = -2*power c x*(∫ t : ℝ in 0..|x|, weight c t*cut t) at read
    rw [read, show out x = _ from outwardRead, outward, ← intervalIntegral.integral_of_le inside, trace]
    have right : IntervalIntegrable (fun t : ℝ => weight c t*cut t) volume |x| r₀ := by
      apply (quarter_positive_domain c cut).mono_set
      rw [uIcc_of_le inside, uIcc_of_le (by norm_num : (0 : ℝ) ≤ q)]
      exact Icc_subset_Icc (abs_nonneg x) (by norm_num)
    have left := compact_weighted_before c cut |x| (abs_nonneg x) (inside.trans (by norm_num))
    rw [← intervalIntegral.integral_add_adjacent_intervals left right]
    ring
  have outer : ∀ᵐ x : ℝ ∂volume, r₀ < |x| → w x = -a*power c x := by
    filter_upwards [compact] with x read beyond
    change w x = -2*power c x*(∫ t : ℝ in 0..|x|, weight c t*cut t) at read
    rw [read, compact_prefix_after c v |x| beyond.le, trace]
    ring
  have Hcentre := (centre_integrable c).coeFn_toL1
  change (out,h)-scaled = splitAtPhysicalCutoff r₀ (R c v)
  apply Prod.ext <;> apply Lp.ext
  · filter_upwards [cutoff_split_read r₀ (R c v), whole, extent, inner, outgoing_centre_read c core,
      Hcentre, Lp.coeFn_sub out scaled.1, Lp.coeFn_smul (2*a) (H c).1]
      with x split read extZero insideR outRead Hread subRead scalar
    change (out-scaled.1 : L¹) x = _
    change (H c).1 x = _ at Hread
    change scaled.1 x = _ at scalar
    rw [subRead, Pi.sub_apply, scalar, Pi.smul_apply, smul_eq_mul, Hread, split.1]
    by_cases inside : x ∈ box
    · rw [indicator_of_mem inside, indicator_of_mem inside, read, extZero (abs_le.mpr inside),
        add_zero, insideR (abs_le.mpr inside)]
      ring
    · have beyond : r₀ < |x| := lt_of_not_ge (fun h => inside (abs_le.mp h))
      rw [indicator_of_notMem inside, indicator_of_notMem inside, mul_zero, sub_zero]
      change outgoingCentre c core x = _
      rw [outRead, Ioc_eq_empty (not_lt.mpr beyond.le), setIntegral_empty, mul_zero]
  · filter_upwards [cutoff_split_read r₀ (R c v), whole, extent, outer, homogeneous_tail_read c,
      Lp.coeFn_sub h scaled.2, Lp.coeFn_smul (2*a) (H c).2]
      with x split read extZero outsideR Hread subRead scalar
    change (h-scaled.2 : BurnolL2) x = _
    change (H c).2 x = _ at Hread
    change scaled.2 x = _ at scalar
    rw [subRead, Pi.sub_apply, scalar, Pi.smul_apply, smul_eq_mul, Hread, split.2]
    by_cases inside : x ∈ box
    · have bounded := abs_le.mpr inside
      rw [if_neg (not_lt_of_ge bounded), mul_zero, sub_zero, extZero bounded,
        indicator_of_mem inside, sub_self]
    · have beyond : r₀ < |x| := lt_of_not_ge (fun h => inside (abs_le.mp h))
      rw [if_pos beyond, indicator_of_notMem inside, sub_zero, read, outsideR beyond]
      ring

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
