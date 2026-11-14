import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.PhysicalJetRate

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource OriginalRieszSourceGreen
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PositionDual
open scoped Topology ENNReal

open private log_stable from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar
open private mean_power from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
open private moment from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel
open private complete_even collar_primitive_source from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar
open private compensated_even from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical
open private elementary_projection from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Physical
open private normalizedEndpoint from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.FixedEndpoints

local notation "q" => (1/4 : ℝ)
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "lead" => ForcingPrimitive.leadingCoefficient
local notation "ζ" => fun c => riemannZeta (s₀ c)
local notation "whole" => fun c => floorFromResponses c+ζ c • elementarySource c
local notation "delta" => fun c (n : Nat) => whole c-compensated c (n+2)
local notation "A" => fun c (n : Nat) => Prod.fst (clockCoefficients c (actualClockPair c n))
local notation "B" => fun c (n : Nat) => Prod.snd (clockCoefficients c (actualClockPair c n))
local notation "R₀" => fun c => burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)
local notation "P" => burnolEvenAmbientProjection
local notation "phase" => fun c (n : Nat) => ((n+2 : Nat) : ℂ)^(-s₀ c)
local notation "clock" => fun (n : Nat) => Real.log ((n+2 : Nat) : ℝ)
local notation "scale" => fun c (n : Nat) => (clock n : ℂ)*phase c n
local notation "μq" => Measure.restrict (volume : Measure ℝ) (Ioc (0 : ℝ) q)

/-- Subtracting the same complete Unit leaves the actual count difference in the
original physical projection's kernel before the original R acts. -/
theorem actual_counted_source_invisible (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    P (delta c n) = 0 := by
  have full : P (whole c) = unitMean c • P ConstantDual.seed := by
    change P (floorFromResponses c+ζ c • elementarySource c) = _
    rw [map_add, map_smul, actual_Pa_limit, elementary_projection]
    module
  have finite : P (compensated c (n+2)) = unitMean c • P ConstantDual.seed := by
    unfold compensated
    rw [map_add, map_smul, actual_finite_Pa c (n+2) (by omega), elementary_projection]
    module
  change P (whole c-compensated c (n+2)) = 0
  rw [map_sub, full, finite, sub_self]

/-- As soon as the literal count covers a positive point, the settled source difference
has only its original normalization coefficient there. -/
theorem actual_settled_count_difference (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    ∀ᵐ x : ℝ ∂volume, 0 < x → x ≤ q → q/x < ((n+2 : Nat) : ℝ) →
      delta c n x = B c n*seedRaw c.value x := by
  have elementary := gapState_read c
  change (elementarySource c : ℝ → ℂ) =ᵐ[volume] _ at elementary
  filter_upwards [Lp.coeFn_sub (whole c) (compensated c (n+2)),
    Lp.coeFn_add (floorFromResponses c) (ζ c • elementarySource c),
    Lp.coeFn_smul (ζ c) (elementarySource c), actual_floor_raw c,
    elementary, actual_compensated_raw c (n+2), log_stable c (n+2)]
    with x difference sum scaled floor unit finite logValue positive bounded covered
  have inWindow : x ∈ symmetricInterval q := ⟨by linarith, bounded⟩
  have visits : q/|x| < ((n+2 : Nat) : ℝ) := by simpa only [abs_of_pos positive] using covered
  have logs : logCount c (n+2) x = logReturnFloor c x := logValue positive.ne' visits
  have positions := PositionCounting.raw_event c (n+2) x positive.ne' visits
  have seed : seedRaw c.value x = (1/2 : ℂ)*powerRaw c.value x-GapEuler.gapMean q c := by
    unfold seedRaw
    linear_combination -mean_power c
  change (whole c-compensated c (n+2) : BurnolL2) x =
    (clockCoefficients c (actualClockPair c n)).2*seedRaw c.value x
  rw [difference, Pi.sub_apply, sum, Pi.add_apply, scaled, Pi.smul_apply, smul_eq_mul,
    floor, actual_counted_position_source c x, unit, gapState_raw_gap c inWindow,
    finite, logs, positions, indicator_of_mem inWindow, actual_clock_coefficients, seed]
  change PositionCounting.eventRaw c x + lead c*logReturnFloor c x -
      (1/2 : ℂ)*powerRaw c.value x*ζ c + ζ c*GapEuler.gapMean q c -
      (lead c*logReturnFloor c x+PositionCounting.eventRaw c x-
        FiniteForcing.coefficient (s₀ c) (n+2)*((1/2 : ℂ)*powerRaw c.value x-GapEuler.gapMean q c)) =
    (FiniteForcing.coefficient (s₀ c) (n+2)-ζ c)*((1/2 : ℂ)*powerRaw c.value x-GapEuler.gapMean q c)
  ring

private theorem outer_is_moment (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    A c n = moment c (delta c n) := by
  change -normalizedEndpoint c q (delta c n) = _
  simp only [normalizedEndpoint, intervalIntegral.integral_same, mul_zero, add_zero, neg_neg]

/-- The original R realizes the same two endpoint coefficients on every settled interior point. -/
theorem actual_settled_R_profile (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    ∀ᵐ x : ℝ ∂volume, 0 < x → x ≤ q → q/x < ((n+2 : Nat) : ℝ) →
      R₀ c (delta c n) x = (x : ℂ)^(-s₀ c)*(-A c n+B c n*collarPrimitive c x) := by
  have even : reflectL2 (delta c n) = delta c n := by
    change reflectL2 (whole c-compensated c (n+2)) = _
    rw [map_sub, complete_even, compensated_even]
  filter_upwards [actual_quarter_endpoint_action c (delta c n) even]
    with x acted positive bounded covered
  have remaining : (∫ y : ℝ in x..q, (y : ℂ)^(s₀ c-1)*delta c n y) =
      B c n*(∫ y : ℝ in x..q, (y : ℂ)^(s₀ c-1)*seedRaw c.value y) := by
    rw [intervalIntegral.integral_of_le bounded, intervalIntegral.integral_of_le bounded,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (actual_settled_count_difference c n),
      ae_restrict_mem measurableSet_Ioc] with y source member
    have ordered : x ≤ y := member.1.le
    have settled : q/y < ((n+2 : Nat) : ℝ) :=
      (div_le_div_of_nonneg_left (by norm_num) positive ordered).trans_lt covered
    rw [source (positive.trans_le ordered) member.2 settled]
    ring
  rw [acted positive bounded, ← outer_is_moment, remaining, ← collar_primitive_source c x positive bounded]
  ring

/-- The complete acted count uses the same phase and log scale as its original K projection. -/
def countedNormalizedField (c : BurnolCompletedMellinCoordinate) (n : Nat) : BurnolL2 :=
  (scale c n)⁻¹ • R₀ c (delta c n)

private theorem count_below_log_scale (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => (scale c n)⁻¹*B c n) atTop (𝓝 0) := by
  have indices : Tendsto (fun n : Nat => ((n+2 : Nat) : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
  have clockLimit : Tendsto (fun n : Nat => (clock n : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
        (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp indices))
  have actual := clockLimit.mul (actual_phase_count_limit c)
  simp only [zero_mul] at actual
  apply actual.congr'
  filter_upwards with n
  change (clock n : ℂ)⁻¹*((phase c n)⁻¹*B c n) = ((clock n : ℂ)*phase c n)⁻¹*B c n
  rw [mul_inv_rev, mul_assoc]
  exact mul_left_comm _ _ _

/-- Every positive interior point is eventually covered by the same counted action. -/
theorem actual_normalized_counted_interior_limit (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂μq, Tendsto (fun n : Nat => countedNormalizedField c n x) atTop
      (𝓝 ((x : ℂ)^(-s₀ c)*(1/2 : ℂ))) := by
  have profile := ae_all_iff.mpr (actual_settled_R_profile c)
  have scaled : ∀ᵐ x : ℝ ∂volume, ∀ n : Nat,
      countedNormalizedField c n x = (scale c n)⁻¹ * R₀ c (delta c n) x := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [Lp.coeFn_smul (scale c n)⁻¹ (R₀ c (delta c n))] with x scaled
    exact scaled
  have indices : Tendsto (fun n : Nat => ((n+2 : Nat) : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
  have outer : Tendsto (fun n : Nat => (scale c n)⁻¹*(-A c n)) atTop (𝓝 (1/2 : ℂ)) := by
    have result := (actual_scaled_outer_limit c).const_mul (1/2 : ℂ)
    simp only [mul_one] at result
    apply result.congr'
    filter_upwards with n
    change (1/2 : ℂ)*((scale c n)⁻¹*(-(2*A c n))) = _
    ring
  filter_upwards [ae_restrict_of_ae profile, ae_restrict_of_ae scaled, ae_restrict_mem measurableSet_Ioc]
    with x field scaledValue inBand
  have full := (outer.add ((count_below_log_scale c).mul_const (collarPrimitive c x))).const_mul ((x : ℂ)^(-s₀ c))
  simp only [zero_mul, add_zero] at full
  apply full.congr'
  filter_upwards [indices.eventually (eventually_gt_atTop (q/x))] with n covered
  rw [scaledValue n, field n inBand.1 inBand.2 covered]
  ring

private theorem singular_limit_not_memLp (c : BurnolCompletedMellinCoordinate) :
    ¬ MemLp (fun x : ℝ => (x : ℂ)^(-s₀ c)*(1/2 : ℂ)) 2 μq := by
  intro admitted
  have square : IntegrableOn (fun x : ℝ => ‖(x : ℂ)^(-s₀ c)*(1/2 : ℂ)‖^2) (Ioc 0 q) :=
    (memLp_two_iff_integrable_sq_norm admitted.aestronglyMeasurable).mp admitted
  have restricted : IntegrableOn (fun x : ℝ => ‖(x : ℂ)^(-s₀ c)*(1/2 : ℂ)‖^2) (Ioo 0 q) :=
    square.mono_set Ioo_subset_Ioc_self
  have halfNorm : ‖(1/2 : ℂ)‖ = 1/2 := by rw [norm_div, norm_one]; norm_num
  have power : IntegrableOn (fun x : ℝ => x^(-2*c.value.re)) (Ioo 0 q) := by
    have weighted : IntegrableOn (fun x : ℝ => 4*‖(x : ℂ)^(-s₀ c)*(1/2 : ℂ)‖^2) (Ioo 0 q) :=
      Integrable.const_mul restricted 4
    apply weighted.congr_fun _ measurableSet_Ioo
    intro x member
    change 4*‖(x : ℂ)^(-s₀ c)*(1/2 : ℂ)‖^2 = x^(-2*c.value.re)
    rw [norm_mul, halfNorm, Complex.norm_cpow_eq_rpow_re_of_pos member.1, mul_pow]
    simp only [neg_re, star_def, conj_re]
    rw [← Real.rpow_mul_natCast member.1.le]
    have exponent : -c.value.re*((2 : ℕ) : ℝ) = -2*c.value.re := by ring
    rw [exponent]
    ring
  have integrable := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < q)).mp power
  linarith [c.rightHalf]

/-- The complete acted field has unbounded normalized L² mass from the original interior source. -/
theorem actual_normalized_counted_norm (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => ‖countedNormalizedField c n‖) atTop atTop := by
  refine tendsto_atTop.2 (fun bound => ?_)
  by_contra late
  have frequent : ∃ᶠ n : Nat in atTop, ‖countedNormalizedField c n‖ < bound :=
    (not_eventually.mp late).mono (fun n hn => lt_of_not_ge hn)
  obtain ⟨index, strict, less⟩ := extraction_of_frequently_atTop frequent
  let values := fun n : Nat => (countedNormalizedField c (index n) : ℝ → ℂ)
  have measurable (n : Nat) : AEStronglyMeasurable (values n) μq :=
    (Lp.aestronglyMeasurable (countedNormalizedField c (index n))).mono_measure Measure.restrict_le_self
  have converges : ∀ᵐ x : ℝ ∂μq,
      Tendsto (fun n => values n x) atTop (𝓝 ((x : ℂ)^(-s₀ c)*(1/2 : ℂ))) := by
    filter_upwards [actual_normalized_counted_interior_limit c] with x actual
    exact actual.comp strict.tendsto_atTop
  have budgets : ∀ᶠ n : Nat in atTop, eLpNorm (values n) 2 μq ≤ ENNReal.ofReal bound := by
    filter_upwards with n
    calc
      _ ≤ eLpNorm (values n) 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = ENNReal.ofReal ‖countedNormalizedField c (index n)‖ :=
        (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (countedNormalizedField c (index n)))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (less n).le
  have finite := Lp.eLpNorm_le_of_ae_tendsto budgets measurable converges
  exact singular_limit_not_memLp c ⟨aestronglyMeasurable_of_tendsto_ae atTop measurable converges,
    finite.trans_lt ENNReal.ofReal_lt_top⟩

/-- The original projection has a finite strong limit, and its actual orthogonal remainder
carries the diverging part of the same normalized action. -/
theorem actual_normalized_counted_remainder_norm (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat =>
      ‖countedNormalizedField c n-(P (countedNormalizedField c n) : BurnolL2)‖) atTop atTop := by
  have physical : Tendsto (fun n => P (countedNormalizedField c n)) atTop
      (𝓝 (burnolCompletedMellinRieszVector c)) := by
    simpa only [countedNormalizedField, map_smul] using actual_scaled_counted_physical_limit c
  have bound : ∀ᶠ n : Nat in atTop, ‖P (countedNormalizedField c n)‖ <
      ‖burnolCompletedMellinRieszVector c‖+1 :=
    physical.norm.eventually (gt_mem_nhds (lt_add_one _))
  refine tendsto_atTop.2 (fun cost => ?_)
  filter_upwards [bound, (tendsto_atTop.1 (actual_normalized_counted_norm c))
    (cost+‖burnolCompletedMellinRieszVector c‖+1)] with n small large
  have tail := norm_sub_norm_le (countedNormalizedField c n) (P (countedNormalizedField c n) : BurnolL2)
  change ‖countedNormalizedField c n‖-‖P (countedNormalizedField c n)‖ ≤ _ at tail
  linarith

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
