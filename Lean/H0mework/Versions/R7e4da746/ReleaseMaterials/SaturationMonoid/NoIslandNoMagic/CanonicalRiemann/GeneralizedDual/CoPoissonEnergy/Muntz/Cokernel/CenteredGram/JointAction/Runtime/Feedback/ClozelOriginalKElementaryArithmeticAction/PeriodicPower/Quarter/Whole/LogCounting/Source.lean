import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Weighted

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Weighted
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKFiniteOrderRelease.UnitPowerJordanAction
open scoped Topology InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "E"=>burnolQuarterZeroExtension
local notation "Rq"=>burnolQuarterRestriction

private theorem weighted_extension_raw (state:Hq) (raw:ℝ→ℂ)
    (represents:(state:ℝ→ℂ)=ᵐ[μq]raw):
    (E (weightQuarter state):ℝ→ℂ)=ᵐ[volume]
      (symmetricInterval q).indicator (fun x:ℝ=>((|x|:ℝ):ℂ)*raw x) := by
  have localRead:∀ᵐx:ℝ∂volume,x∈symmetricInterval q→
      weightQuarter state x=((|x|:ℝ):ℂ)*raw x := by
    apply (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    filter_upwards [actual_weight_raw state,represents] with x weight read
    rw [weight,read]
  filter_upwards [burnolQuarterZeroExtension_coe (weightQuarter state),localRead] with x extended read
  rw [extended]
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,indicator_of_mem inside,read inside]
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

private def weightedRawTerm (raw:ℝ→ℂ) (n:ℕ) (x:ℝ):ℂ :=
  ((|x|:ℝ):ℂ)*(symmetricInterval q).indicator raw ((n+1:ℕ)*x)

private theorem weighted_term_raw (state:Hq) (raw:ℝ→ℂ)
    (represents:(state:ℝ→ℂ)=ᵐ[μq]raw) (n:ℕ):
    (weightedTerm state n:ℝ→ℂ)=ᵐ[volume]weightedRawTerm raw n := by
  have positive:(0:ℝ)<(n+1:ℕ):=by positivity
  have native:=DualSourceRaw.channel_coeFn _ _ (weighted_extension_raw state raw represents)
    ((n+1:ℕ):ℝ) positive
  filter_upwards [native,Lp.coeFn_smul (((n+1:ℕ):ℂ)⁻¹)
    (ContinuousChannels.channel 1 (n+1:ℕ) (E (weightQuarter state)))] with x counted scalar
  change weightedTerm state n x=_ at scalar
  rw [scalar,Pi.smul_apply,smul_eq_mul,counted,weightedRawTerm]
  by_cases inside:((n+1:ℕ):ℝ)*x∈symmetricInterval q
  · rw [indicator_of_mem inside,indicator_of_mem inside,abs_mul,abs_of_pos positive,Complex.ofReal_mul]
    simp only [Complex.ofReal_natCast]
    field_simp
  · rw [indicator_of_notMem inside,indicator_of_notMem inside,mul_zero,mul_zero]

/-- This is the original finite grid, including its actual q endpoint and every positive integer. -/
def arithmeticRaw (raw:ℝ→ℂ) (x:ℝ):ℂ :=
  ((|x|:ℝ):ℂ)*∑n∈DualSourceRaw.channels x,raw ((n:ℝ)*x)

private theorem shifted_sum (N:ℕ) (f:ℕ→ℂ):
    (∑n∈Finset.range N,f (n+1))=∑n∈Finset.Icc 1 N,f n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,Finset.sum_Icc_succ_top (by omega)]

private theorem raw_sum (raw:ℝ→ℂ) (x:ℝ):
    (∑'n:ℕ,weightedRawTerm raw n x)=arithmeticRaw raw x := by
  classical
  by_cases atZero:x=0
  · subst x
    simp [weightedRawTerm,arithmeticRaw]
  · let N:ℕ:=⌊q/|x|⌋₊
    have incidence (n:ℕ) (positive:0<n):
        (n:ℝ)*x∈symmetricInterval q↔n∈DualSourceRaw.channels x := by
      simp only [DualSourceRaw.channels,Finset.mem_Icc,show 1≤n from positive,true_and,
        symmetricInterval,mem_Icc,←abs_le,abs_mul,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n),
        Nat.le_floor_iff' positive.ne',le_div_iff₀ (abs_pos.mpr atZero)]
    rw [tsum_eq_sum (s:=Finset.range N) (fun n outside=>by
      have index:N≤n:=le_of_not_gt (fun h=>outside (Finset.mem_range.mpr h))
      have excluded:((n+1:ℕ):ℝ)*x∉symmetricInterval q := by
        intro h
        have bound: n+1≤N:=(Finset.mem_Icc.mp ((incidence (n+1) (by omega)).mp h)).2
        omega
      rw [weightedRawTerm,indicator_of_notMem excluded,mul_zero])]
    have active:∀n∈Finset.range N,weightedRawTerm raw n x=
        ((|x|:ℝ):ℂ)*raw ((n+1:ℕ)*x) := by
      intro n hn
      have belongs:n+1∈DualSourceRaw.channels x:=Finset.mem_Icc.mpr ⟨by omega,
        by change n+1≤N;have:=Finset.mem_range.mp hn;omega⟩
      rw [weightedRawTerm,indicator_of_mem ((incidence _ (by omega)).mpr belongs)]
    rw [Finset.sum_congr rfl active,←Finset.mul_sum,shifted_sum N (fun n=>raw ((n:ℝ)*x))]
    rfl

theorem actual_arithmetic_field (state:Hq) (raw:ℝ→ℂ)
    (represents:(state:ℝ→ℂ)=ᵐ[μq]raw):
    (weightedCount state:ℝ→ℂ)=ᵐ[volume]arithmeticRaw raw := by
  have summation:=Lp.hasSum_coeFn_tsum
    (tsum_enorm_ne_top_iff_summable_norm.mpr (actual_weighted_norm_summable state))
  have terms:∀ᵐx:ℝ∂volume,∀n:ℕ,weightedTerm state n x=weightedRawTerm raw n x:=
    ae_all_iff.mpr (weighted_term_raw state raw represents)
  filter_upwards [summation,terms] with x sum read
  have actual:=sum.congr_fun (fun n=>(read n).symm)
  exact actual.tsum_eq.symm.trans (raw_sum raw x)

def logFirstCount (d:BurnolCompletedMellinCoordinate) (k:ℕ):BurnolL2:=
  weightedCount (logBFirst d k:Hq)

def logSecondCount (d:BurnolCompletedMellinCoordinate) (k:ℕ):BurnolL2:=
  weightedCount (logBSecond d k:Hq)

theorem actual_log_first_field (d:BurnolCompletedMellinCoordinate) (k:ℕ):
    (logFirstCount d k:ℝ→ℂ)=ᵐ[volume]arithmeticRaw (logFirstRaw d k):=
  actual_arithmetic_field _ _ (log_first_profile d k)

theorem actual_log_second_field (d:BurnolCompletedMellinCoordinate) (k:ℕ):
    (logSecondCount d k:ℝ→ℂ)=ᵐ[volume]
      arithmeticRaw (fun x=>-burnolMeanZeroFourierRaw (logBFirst d k) x) := by
  apply actual_arithmetic_field
  filter_upwards [Lp.coeFn_neg (burnolMeanZeroTruncatedFourier (logBFirst d k):Hq),
    burnolMeanZeroFourier_ae_raw (logBFirst d k)] with x negative raw
  change (-(burnolMeanZeroTruncatedFourier (logBFirst d k):Hq)) x=_ at negative ⊢
  rw [negative,Pi.neg_apply,raw]

/-- Every first-foot log column now has a genuine native arithmetic cotest, with the weight cancelled in price. -/
theorem actual_log_first_native_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (k:ℕ):
    inner ℂ (logBFirst d k:Hq) (forwardQuarter c zero)=
      inner ℂ (logFirstCount d k) (E (normalizedRegular c zero)) :=
  (actual_weighted_native_price c zero _).symm

theorem actual_log_second_native_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (k:ℕ):
    inner ℂ (logBSecond d k:Hq) (forwardQuarter c zero)=
      inner ℂ (logSecondCount d k) (E (normalizedRegular c zero)) :=
  (actual_weighted_native_price c zero _).symm

private theorem native_finite_limit (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (state:M):
    Tendsto (fun N:ℕ=>inner ℂ (DualSource.source N (E (state:Hq))) (regularSource c zero)) atTop
      (𝓝 (inner ℂ (weightedCount (state:Hq)) (E (normalizedRegular c zero)))) := by
  have finite (N:ℕ):inner ℂ (DualSource.source N (E (state:Hq))) (regularSource c zero)=
      inner ℂ (state:Hq) (Rq (FiniteForcing.source N (regularSource c zero))) := by
    have source:=congrArg star (CountingDual.source_pairing N (regularSource c zero) (E (state:Hq)))
    simp only [star_def,inner_conj_symm] at source
    rw [←source]
    exact ContinuousLinearMap.adjoint_inner_left Rq _ _
  have source:=(tendsto_const_nhds (x:=(state:Hq))).inner (𝕜:=ℂ) (actual_regular_counting_limit c zero)
  have mean:inner ℂ (state:Hq) (intervalConstant q)=0 := by
    apply inner_eq_zero_symm.mp
    exact (Submodule.mem_orthogonal _ _).mp state.property _ (Submodule.mem_span_singleton_self _)
  rw [inner_sub_right,inner_smul_right,mean,mul_zero,sub_zero,←actual_weighted_native_price] at source
  exact source.congr' (Eventually.of_forall (fun N=>(finite N).symm))

theorem actual_log_first_native_limit (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (k:ℕ):
    Tendsto (fun N:ℕ=>inner ℂ (DualSource.source N (E (logBFirst d k:Hq))) (regularSource c zero)) atTop
      (𝓝 (inner ℂ (logFirstCount d k) (E (normalizedRegular c zero)))) :=
  native_finite_limit c zero _

theorem actual_log_second_native_limit (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (k:ℕ):
    Tendsto (fun N:ℕ=>inner ℂ (DualSource.source N (E (logBSecond d k:Hq))) (regularSource c zero)) atTop
      (𝓝 (inner ℂ (logSecondCount d k) (E (normalizedRegular c zero)))) :=
  native_finite_limit c zero _

private theorem native_finite_mean (N:ℕ) (positive:0<N) (state:M):
    burnolQuarterMeanCoefficient (Rq (DualSource.source N (E (state:Hq))))=
      2*inner ℂ SmallScaleLog.logL2 (state:Hq) := by
  have pair:inner ℂ (intervalConstant q) (Rq (DualSource.source N (E (state:Hq))))=
      inner ℂ (WindowCounting.windowSource N (intervalConstant q)) (state:Hq) := by
    calc
      _=inner ℂ (E (intervalConstant q)) (DualSource.source N (E (state:Hq))):=
        (ContinuousLinearMap.adjoint_inner_left Rq _ _).symm
      _=inner ℂ (FiniteForcing.source N (E (intervalConstant q))) (E (state:Hq)):=
        (CountingDual.source_pairing N _ _).symm
      _=_:=ContinuousLinearMap.adjoint_inner_right Rq _ _
  have mean:inner ℂ (intervalConstant q) (state:Hq)=0:=
    (Submodule.mem_orthogonal _ _).mp state.property _ (Submodule.mem_span_singleton_self _)
  unfold burnolQuarterMeanCoefficient
  rw [pair,WindowCounting.constant_source N positive,inner_add_left,inner_smul_left,
    mean,mul_zero,zero_add,Complex.ofReal_pow,burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)]
  norm_num
  ring

/-- The original logarithmic mean survives at every cutoff, for both generated feet. -/
theorem actual_log_native_means (d:BurnolCompletedMellinCoordinate) (k N:ℕ) (positive:0<N):
    burnolQuarterMeanCoefficient (Rq (DualSource.source N (E (logBFirst d k:Hq))))=
      2*inner ℂ SmallScaleLog.logL2 (logBFirst d k:Hq) ∧
    burnolQuarterMeanCoefficient (Rq (DualSource.source N (E (logBSecond d k:Hq))))=
      2*inner ℂ SmallScaleLog.logL2 (logBSecond d k:Hq) :=
  ⟨native_finite_mean N positive _,native_finite_mean N positive _⟩

/-- The actual complete finite-order outside bank is consumed as one native source field. -/
theorem actual_full_log_bank_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (j:ℕ):
    (∑k∈Finset.range j,star (sourceCoefficient d j k)*
      inner ℂ (logBFirst d k:Hq) (forwardQuarter c zero))=
      inner ℂ (∑k∈Finset.range j,sourceCoefficient d j k • logFirstCount d k)
        (E (normalizedRegular c zero)) := by
  simp only [sum_inner,inner_smul_left,starRingEnd_apply,actual_log_first_native_price]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
