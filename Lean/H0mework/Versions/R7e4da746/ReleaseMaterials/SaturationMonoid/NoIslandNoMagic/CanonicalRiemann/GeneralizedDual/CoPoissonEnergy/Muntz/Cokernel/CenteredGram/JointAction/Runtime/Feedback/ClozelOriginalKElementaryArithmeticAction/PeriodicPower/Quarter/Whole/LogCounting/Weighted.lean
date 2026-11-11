import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.NativeContact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Weighted
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward InverseAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKFiniteOrderRelease.UnitPowerJordanAction
open scoped Topology InnerProductSpace
open private integer_sum window_norm_summable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting
local notation "q"=>(1/4:ℝ)
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "E"=>burnolQuarterZeroExtension
local notation "Rq"=>burnolQuarterRestriction
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem weight_memLp (state:Hq):MemLp (fun x:ℝ=>((|x|:ℝ):ℂ)*state x) 2 μq := by
  apply (Lp.memLp state).of_le_mul (c:=q)
    ((Complex.continuous_ofReal.comp continuous_abs).aestronglyMeasurable.mul (Lp.aestronglyMeasurable state))
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
  change ‖((|x|:ℝ):ℂ)*state x‖≤q*‖state x‖
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_abs]
  exact mul_le_mul_of_nonneg_right (abs_le.mpr inside) (norm_nonneg _)

def weightQuarter (state:Hq):Hq := (weight_memLp state).toLp (fun x:ℝ=>((|x|:ℝ):ℂ)*state x)

theorem actual_weight_raw (state:Hq):
    (weightQuarter state:ℝ→ℂ)=ᵐ[μq]fun x:ℝ=>((|x|:ℝ):ℂ)*state x := (weight_memLp state).coeFn_toLp

theorem actual_weight_pair (left right:Hq):
    inner ℂ (weightQuarter left) right=inner ℂ left (weightQuarter right) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [actual_weight_raw left,actual_weight_raw right] with x a b
  rw [a,b]
  change inner ℂ (((|x|:ℝ):ℂ) • left x) (right x)=inner ℂ (left x) (((|x|:ℝ):ℂ) • right x)
  rw [inner_smul_left,inner_smul_right]
  congr 1
  exact Complex.conj_ofReal |x|

theorem actual_weight_counting (a:ℝ) (large:1≤a) (state:Hq):
    countingWindow a (weightQuarter state)=(a:ℂ)⁻¹ • weightQuarter (countingWindow a state) := by
  have positive:0<a:=zero_lt_one.trans_le large
  apply Lp.ext
  filter_upwards [countingWindow_raw a positive (weightQuarter state) _ (actual_weight_raw state),
    countingWindow_raw a positive state state (EventuallyEq.rfl),
    actual_weight_raw (countingWindow a state),Lp.coeFn_smul ((a:ℂ)⁻¹) (weightQuarter (countingWindow a state)),
    ae_restrict_mem (measurableSet_symmetricInterval q)] with x weighted raw outer scalar inside
  have moved:x/a∈symmetricInterval q := by
    apply abs_le.mp
    rw [abs_div,abs_of_pos positive,div_le_iff₀ positive]
    have bounded:=abs_le.mpr inside
    nlinarith
  rw [weighted,scalar,Pi.smul_apply,smul_eq_mul,outer,raw]
  simp only [countingRaw,indicator_of_mem moved,abs_div,abs_of_pos positive,Complex.ofReal_div]
  ring

/-- Every channel is the original reverse dilation, with its actual |x| weight transported. -/
def weightedTerm (state:Hq) (n:ℕ):BurnolL2 :=
  (((n+1:ℕ):ℂ)⁻¹) • ContinuousChannels.channel 1 (n+1:ℕ) (E (weightQuarter state))

theorem actual_weighted_term_norm (state:Hq) (n:ℕ):
    ‖weightedTerm state n‖=((n+1:ℕ):ℝ)^(-(3/2:ℝ))*‖E (weightQuarter state)‖ := by
  have positive:(0:ℝ)<(n+1:ℕ):=by positivity
  have scalar:(((n+1:ℕ):ℝ)⁻¹)*(Real.sqrt ((n+1:ℕ):ℝ))⁻¹=
      ((n+1:ℕ):ℝ)^(-(3/2:ℝ)) := by
    rw [←Real.rpow_neg_one,Real.sqrt_eq_rpow,←Real.rpow_neg positive.le,←Real.rpow_add positive]
    congr 1
    norm_num
  simp only [weightedTerm,ContinuousChannels.channel,norm_smul,norm_inv,Complex.norm_natCast,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    (burnolMultiplicativeDilation _).norm_map]
  rw [←mul_assoc,scalar]

theorem actual_weighted_norm_summable (state:Hq):
    Summable (fun n:ℕ=>‖weightedTerm state n‖) := by
  have power:Summable (fun n:ℕ=>(n:ℝ)^(-(3/2:ℝ))):=
    Real.summable_nat_rpow.mpr (by norm_num)
  have shifted:Summable (fun n:ℕ=>((n+1:ℕ):ℝ)^(-(3/2:ℝ))):=
    (summable_nat_add_iff 1).mpr power
  simpa only [actual_weighted_term_norm] using shifted.mul_right ‖E (weightQuarter state)‖

def weightedCount (state:Hq):BurnolL2:=∑'n:ℕ,weightedTerm state n

theorem actual_weighted_term_pair (state test:Hq) (n:ℕ):
    inner ℂ (weightedTerm state n) (E test)=
      inner ℂ state (countingWindow (n+1:ℕ) (weightQuarter test)) := by
  have positive:(0:ℝ)<(n+1:ℕ):=by positivity
  have paired:=congrArg star (ContinuousChannels.channel_pairing (n+1:ℕ) (E test) (E (weightQuarter state)))
  simp only [star_def,inner_conj_symm] at paired
  rw [weightedTerm,inner_smul_left]
  simp only [starRingEnd_apply,star_inv₀,star_natCast]
  rw [←paired,show E=burnolQuarterRestriction.adjoint from rfl,ContinuousLinearMap.adjoint_inner_left,←show E=burnolQuarterRestriction.adjoint from rfl,
    ←WholeSourceWindow.window_channel,
    actual_weight_pair,actual_weight_counting (n+1:ℕ) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)),
    inner_smul_right]
  simp only [Complex.ofReal_natCast]

def normalizedRegularRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ :=
  regularCompactRaw c x/((|x|:ℝ):ℂ)

private theorem normalized_regular_memLp (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):MemLp (normalizedRegularRaw c) 2 μq := by
  obtain ⟨B,nonnegative,growth⟩:=actual_regular_global_growth c zero
  have measured:Measurable (normalizedRegularRaw c):=
    (actual_regular_measurable c).div (Complex.continuous_ofReal.comp continuous_abs).measurable
  apply MemLp.of_bound measured.aestronglyMeasurable B
  filter_upwards with x
  by_cases atZero:x=0
  · simp [normalizedRegularRaw,atZero,nonnegative]
  · rw [normalizedRegularRaw,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_abs]
    exact (div_le_iff₀ (abs_pos.mpr atZero)).mpr (growth x)

def normalizedRegular (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):Hq :=
  (normalized_regular_memLp c zero).toLp (normalizedRegularRaw c)

theorem actual_normalized_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (normalizedRegular c zero:ℝ→ℂ)=ᵐ[μq] normalizedRegularRaw c :=
  (normalized_regular_memLp c zero).coeFn_toLp

theorem actual_normalized_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    weightQuarter (normalizedRegular c zero)=regularQuarter c zero := by
  apply Lp.ext
  filter_upwards [actual_weight_raw (normalizedRegular c zero),actual_normalized_raw c zero,
    actual_regular_quarter_raw c zero,ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with x weight raw regular nonzero
  rw [weight,raw,regular,normalizedRegularRaw]
  field_simp [Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)]

/-- The whole actual r source consumes the complete arithmetic field for every generated cotest. -/
theorem actual_weighted_native_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (state:Hq):
    inner ℂ (weightedCount state) (E (normalizedRegular c zero))=
      inner ℂ state (forwardQuarter c zero) := by
  have left:HasSum (fun n:ℕ=>inner ℂ (weightedTerm state n) (E (normalizedRegular c zero)))
      (inner ℂ (weightedCount state) (E (normalizedRegular c zero))):=
    (actual_weighted_norm_summable state).of_norm.hasSum.mapL (innerSLFlip ℂ (E (normalizedRegular c zero)))
  have normSum:=window_norm_summable c zero
  have shifted:Summable (fun n:ℕ=>countingWindow ((n+1:ℕ):ℝ) (regularQuarter c zero)):=
    (summable_nat_add_iff 1).mpr normSum.of_norm
  have sum:(∑'n:ℕ,countingWindow ((n+1:ℕ):ℝ) (regularQuarter c zero))=forwardQuarter c zero := by
    have source:=normSum.of_norm.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one,Nat.cast_zero,
      show countingWindow (0:ℝ) (regularQuarter c zero)=0 by simp [countingWindow],zero_add,integer_sum] at source
    exact source
  have right:HasSum (fun n:ℕ=>inner ℂ state (countingWindow ((n+1:ℕ):ℝ) (regularQuarter c zero)))
      (inner ℂ state (forwardQuarter c zero)):=by
    rw [←sum]
    exact shifted.hasSum.mapL (innerSL ℂ state)
  apply HasSum.unique _ right
  exact left.congr_fun (fun n=>by rw [actual_weighted_term_pair,actual_normalized_source])

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Weighted
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
