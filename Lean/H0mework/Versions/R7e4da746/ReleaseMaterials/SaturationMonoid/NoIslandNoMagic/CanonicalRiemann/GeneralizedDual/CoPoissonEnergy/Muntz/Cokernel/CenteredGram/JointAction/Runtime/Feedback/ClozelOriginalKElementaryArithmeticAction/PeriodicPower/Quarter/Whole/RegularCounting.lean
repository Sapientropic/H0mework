import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientContinuousMean

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward InverseAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ReciprocalMoment OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionHead OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open scoped Topology InnerProductSpace
open private window_limit from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WholeSourceWindow
open private forward_reindex from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
local notation "q"=>(1/4:ℝ)
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "Rq"=>burnolQuarterRestriction
local notation "Eq"=>burnolQuarterZeroExtension

def regularQuarter (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):Hq:=
  Rq (regularSource c zero)

theorem actual_regular_quarter_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (regularQuarter c zero:ℝ→ℂ)=ᵐ[μq]regularCompactRaw c:=by
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (regularSource c zero),
    ae_restrict_of_ae (actual_regular_source_raw c zero)] with x restricted raw
  exact restricted.trans raw

private theorem compact_indicator (c:BurnolCompletedMellinCoordinate):
    (symmetricInterval q).indicator (regularCompactRaw c)=regularCompactRaw c:=by
  funext x
  by_cases inside:x∈symmetricInterval q
  · exact indicator_of_mem inside _
  · rw [indicator_of_notMem inside,actual_regular_outer_zero c x
      (le_of_not_ge (fun small=>inside (abs_le.mp small)))]

theorem actual_regular_extension (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Eq (regularQuarter c zero)=regularSource c zero:=by
  apply Lp.ext
  have rawLocal:∀ᵐx∂volume,x∈symmetricInterval q→
      regularQuarter c zero x=regularCompactRaw c x:=
    (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (actual_regular_quarter_raw c zero)
  filter_upwards [burnolQuarterZeroExtension_coe (regularQuarter c zero),
    actual_regular_source_raw c zero,rawLocal] with x extended raw localRead
  rw [extended,raw]
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,localRead inside]
  · rw [indicator_of_notMem inside,actual_regular_outer_zero c x
      (le_of_not_ge (fun small=>inside (abs_le.mp small)))]

private theorem window_zero (state:Hq):countingWindow 0 state=0:=by simp [countingWindow]

private theorem constant_norm:‖intervalConstant q‖≤(1:ℝ):=by
  have square:‖intervalConstant q‖^2=2*q:=by
    exact_mod_cast burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)
  norm_num at square
  nlinarith [norm_nonneg (intervalConstant q)]

private theorem window_bound (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (L:ℝ) (nonnegative:0≤L) (growth:∀x:ℝ,‖regularCompactRaw c x‖≤L*|x|)
    (a:ℝ) (large:1≤a):‖countingWindow a (regularQuarter c zero)‖≤(L*q)*a⁻¹^2:=by
  have positive:0<a:=zero_lt_one.trans_le large
  have compared:‖countingWindow a (regularQuarter c zero)‖≤
      ((L*q)*a⁻¹^2)*‖intervalConstant q‖:=by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [countingWindow_raw a positive (regularQuarter c zero) (regularCompactRaw c)
      (actual_regular_quarter_raw c zero),intervalConstant_coeFn q,
      ae_restrict_mem (measurableSet_symmetricInterval q)] with x raw constant inside
    rw [raw,constant,norm_one,mul_one,countingRaw,compact_indicator,norm_mul,norm_inv,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
    calc
      _≤a⁻¹*(L*|x/a|):=mul_le_mul_of_nonneg_left (growth _) (inv_nonneg.mpr positive.le)
      _≤a⁻¹*(L*(q/a)):=by
        rw [abs_div,abs_of_pos positive]
        gcongr
        exact abs_le.mpr inside
      _=(L*q)*a⁻¹^2:=by rw [div_eq_mul_inv];ring
  exact compared.trans (mul_le_of_le_one_right (by positivity) constant_norm)

private theorem window_norm_summable (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Summable (fun n:ℕ=>‖countingWindow (n:ℝ) (regularQuarter c zero)‖):=by
  obtain ⟨L,nonnegative,growth⟩:=actual_regular_global_growth c zero
  have powers:Summable (fun n:ℕ=>(n:ℝ)⁻¹^2):=by
    simpa only [inv_pow] using (Real.summable_nat_pow_inv.mpr (by norm_num : 1<(2:ℕ)))
  apply (powers.mul_left (L*q)).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro n
  by_cases atZero:n=0
  · simp [atZero,window_zero]
  · exact window_bound c zero L nonnegative growth n
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr atZero)

private theorem window_integrable (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    IntegrableOn (fun a:ℝ=>countingWindow a (regularQuarter c zero)) (Ioi 0):=by
  obtain ⟨L,nonnegative,growth⟩:=actual_regular_global_growth c zero
  have powers:IntegrableOn (fun a:ℝ=>a⁻¹^2) (Ioi 1):=by
    simpa only [show (-2:ℝ)=-(2:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,zpow_natCast,inv_pow]
      using (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) (by norm_num : (0:ℝ)<1))
  have tail:IntegrableOn (fun a:ℝ=>countingWindow a (regularQuarter c zero)) (Ioi 1):=by
    apply (powers.const_mul (L*q)).mono'
      (((WholeSourceWindow.window_continuousOn _).mono
        (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a large
    exact window_bound c zero L nonnegative growth a large.le
  have full:=(WholeSourceWindow.window_integrable_local 1 (regularQuarter c zero)).union tail
  rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1)] at full

private theorem integer_sum (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (∑'n:ℕ,countingWindow (n:ℝ) (regularQuarter c zero))=forwardQuarter c zero:=by
  have normSum:=window_norm_summable c zero
  have normShift:Summable (fun n:ℕ=>‖countingWindow ((n+1:ℕ):ℝ) (regularQuarter c zero)‖):=
    (summable_nat_add_iff 1).mpr normSum
  have pointwise:=Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr normShift)
  have terms:∀ᵐx:ℝ∂μq,∀n:ℕ,
      (countingWindow ((n+1:ℕ):ℝ) (regularQuarter c zero):Hq) x=
        ((n+1:ℕ):ℂ)⁻¹*regularCompactRaw c (x/(n+1:ℕ)):=by
    rw [ae_all_iff]
    intro n
    have raw:=countingWindow_raw ((n+1:ℕ):ℝ) (by positivity) (regularQuarter c zero)
      (regularCompactRaw c) (actual_regular_quarter_raw c zero)
    filter_upwards [raw] with x source
    change (countingWindow ((n+1:ℕ):ℝ) (regularQuarter c zero):Hq) x=
      countingRaw ((n+1:ℕ):ℝ) (regularCompactRaw c) x at source
    rw [countingRaw,compact_indicator] at source
    simpa only [Complex.ofReal_natCast] using source
  have sumSame:(∑'n:ℕ,countingWindow ((n+1:ℕ):ℝ) (regularQuarter c zero))=forwardQuarter c zero:=by
    apply Lp.ext
    filter_upwards [pointwise,terms,actual_forward_quarter_raw c zero] with x sumAt actual target
    rw [target]
    have source:HasSum (fun n:ℕ=>((n+1:ℕ):ℂ)⁻¹*regularCompactRaw c (x/(n+1:ℕ)))
        (burnolInnerGapForward (regularCompactRaw c) x):=by
      rw [forward_reindex]
      exact (actual_head_channels c zero x).of_norm.hasSum
    exact (sumAt.congr_fun (fun n=>(actual n).symm)).unique source
  have shifted:=normSum.of_norm.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one,Nat.cast_zero,show countingWindow (0:ℝ) (regularQuarter c zero)=0 from window_zero _,
    zero_add] at shifted
  exact shifted.symm.trans sumSame

/-- The finite programme's complete scale integral keeps the original reciprocal Unit. -/
theorem actual_continuous_normalization (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    (∫a:ℝ in Ioi 0,countingWindow a (regularQuarter c zero))=
      regularReciprocalMean c • intervalConstant q:=by
  have native:=AmbientContinuousMean.countingWindow_integral (regularQuarter c zero) (regularCompactRaw c)
    (actual_regular_measurable c) (actual_regular_even c) (actual_regular_quarter_raw c zero)
    (window_integrable c zero)
  have same:(∫t:ℝ in Ioc (0:ℝ) q,(t:ℂ)⁻¹*regularCompactRaw c t)=regularReciprocalMean c:=by
    rw [regularReciprocalMean,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q),
      integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo (fun x hx=>by
      rw [actual_regular_positive_read c x hx.1 hx.2])
  rwa [same] at native

/-- The actual full regular source pays the missing same-N quarter strong limit. -/
theorem actual_regular_counting_limit (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    Tendsto (fun N:ℕ=>Rq (FiniteForcing.source N (regularSource c zero))) atTop
      (𝓝 (forwardQuarter c zero-regularReciprocalMean c • intervalConstant q)):=by
  have native:=window_limit (regularQuarter c zero) (window_norm_summable c zero).of_norm
    (window_integrable c zero)
  simp_rw [actual_regular_extension] at native
  rwa [integer_sum,actual_continuous_normalization] at native

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
