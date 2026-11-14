import Mathlib.NumberTheory.Harmonic.Bounds
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.NativeReturnImpulse

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.CountedGapVisibility

open BurnolPhysicalState MeasureTheory Set Filter
open BurnolPhysicalState.OriginalRSourceJointContact.OutsideHistory
open scoped InnerProductSpace

attribute [local instance] OriginalKCombCofinalPaAction.physicalComplete

open private gap_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientMellin
open private projected_source from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.FirstPaReturn
open private unit_invisible from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.NativeReturnImpulse

local notation "E" => OriginalKCombCofinalPaAction.E
local notation "D" => burnolMultiplicativeDilation
local notation "q" => burnolUnscaledCommonGapRadius
local notation "window" => symmetricInterval q
local notation "H" => burnolUnitCountingPrimitiveL2
local notation "Hraw" => burnolUnitCountingPrimitiveRaw
local notation "W" => burnolReciprocalStepNativeWave 1 2

private def loss (x : ℝ) : ℝ := ‖Hraw x‖

private theorem loss_integrable (a b : ℝ) : IntervalIntegrable loss volume a b := by
  apply (intervalIntegrable_iff' (f := loss) (μ := (volume : Measure ℝ))).mpr
  exact (burnolUnitCountingPrimitive_memLp.norm.locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_uIcc

private theorem raw_real_nonpos (x : ℝ) : ∃ r : ℝ, r ≤ 0 ∧ Hraw x = r := by
  by_cases zero : x = 0
  · subst x
    exact ⟨-1,by norm_num,by simp [burnolUnitCountingPrimitiveRaw]⟩
  · have positive := abs_pos.mpr zero
    have near := Nat.ceil_lt_add_one (abs_nonneg x)
    refine ⟨((⌈|x|⌉₊ : ℝ)-1) / |x| - 1, ?_, ?_⟩
    · have below : (⌈|x|⌉₊ : ℝ)-1 ≤ |x| := by linarith
      exact sub_nonpos.mpr ((div_le_one₀ positive).mpr below)
    · simp only [burnolUnitCountingPrimitiveRaw,zero,if_false]

private theorem raw_conj (x : ℝ) : star (Hraw x) = -(loss x : ℂ) := by
  obtain ⟨r,negative,actual⟩ := raw_real_nonpos x
  have conjugate : star (r:ℂ) = (r:ℂ) := Complex.conj_ofReal r
  rw [actual,conjugate,loss,actual,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos negative]
  simp only [Complex.ofReal_neg,neg_neg]

private theorem half_block (n : Nat) {x : ℝ} (inside : x ∈ Icc ((n:ℝ)+1/2) ((n:ℝ)+1)) :
    1/(2*((n:ℝ)+1)) ≤ loss x := by
  have positive : 0 < x := by have nonneg : 0 ≤ (n:ℝ) := Nat.cast_nonneg _; linarith [inside.1]
  have nBelow : (n:ℝ) < x := by linarith [inside.1]
  have ceiling : ⌈x⌉₊ = n+1 := by
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero n)]
    push_cast
    exact ⟨by linarith,inside.2⟩
  have form : Hraw x = (((n:ℝ)/x-1 : ℝ):ℂ) := by
    simp [burnolUnitCountingPrimitiveRaw,positive.ne',ceiling,Nat.cast_succ,abs_of_pos positive]
  have negative : (n:ℝ)/x-1 ≤ 0 := sub_nonpos.mpr ((div_le_one₀ positive).mpr nBelow.le)
  rw [loss,form,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos negative]
  have next : 0 < (n:ℝ)+1 := by positivity
  calc
    1/(2*((n:ℝ)+1)) = (1/2)/((n:ℝ)+1) := by field_simp
    _ ≤ (x-(n:ℝ))/((n:ℝ)+1) := div_le_div_of_nonneg_right (by linarith [inside.1]) next.le
    _ ≤ (x-(n:ℝ))/x := div_le_div_of_nonneg_left (sub_nonneg.mpr nBelow.le) positive inside.2
    _ = -((n:ℝ)/x-1) := by rw [sub_div,div_self positive.ne']; ring

private theorem block_mass (n : Nat) :
    1/(4*((n:ℝ)+1)) ≤ ∫ x in (n:ℝ)..((n:ℝ)+1), loss x := by
  have left : (n:ℝ) ≤ (n:ℝ)+1/2 := by linarith
  have right : (n:ℝ)+1/2 ≤ (n:ℝ)+1 := by linarith
  have nonnegative : 0 ≤ ∫ x in (n:ℝ)..((n:ℝ)+1/2), loss x :=
    intervalIntegral.integral_nonneg left (fun x _ => norm_nonneg (Hraw x))
  have lower := intervalIntegral.integral_mono_on right
    (intervalIntegrable_const (c := (1/(2*((n:ℝ)+1))))) (loss_integrable _ _)
    (fun _ inside => half_block n inside)
  have whole := intervalIntegral.integral_add_adjacent_intervals
    (loss_integrable (n:ℝ) ((n:ℝ)+1/2)) (loss_integrable ((n:ℝ)+1/2) ((n:ℝ)+1))
  rw [intervalIntegral.integral_const,smul_eq_mul] at lower
  rw [← whole]
  have half : (((n:ℝ)+1)-((n:ℝ)+1/2)) * (1/(2*((n:ℝ)+1))) = 1/(4*((n:ℝ)+1)) := by field_simp; ring
  rw [half] at lower
  linarith

private theorem harmonic_mass (n : Nat) :
    ((harmonic n : ℚ) : ℝ)/4 ≤ ∫ x in (0:ℝ)..(n:ℝ), loss x := by
  induction n with
  | zero => simp [harmonic]
  | succ n previous =>
    have step : ((harmonic (n+1) : ℚ):ℝ)/4 =
        ((harmonic n : ℚ):ℝ)/4 + 1/(4*((n:ℝ)+1)) := by
      rw [harmonic_succ,Rat.cast_add,Rat.cast_inv,Rat.cast_natCast,Nat.cast_succ]
      field_simp
    have whole := intervalIntegral.integral_add_adjacent_intervals
      (loss_integrable 0 (n:ℝ)) (loss_integrable (n:ℝ) ((n:ℝ)+1))
    rw [step,Nat.cast_succ,← whole]
    exact add_le_add previous (block_mass n)

private def scaled (a : ℝ) : BurnolL2 := burnolSourceScalePrimitive H a

private theorem scaled_raw (a : ℝ) (positive : 0 < a) :
    (scaled a : ℝ → ℂ) =ᵐ[volume] fun x => (a:ℂ)*Hraw (a*x) :=
  burnolSourceScalePrimitive_coeFn H Hraw burnolUnitCountingPrimitive_memLp.coeFn_toLp a positive

private def reciprocalTail : BurnolL2 := burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 4

private def tailBudget (value : BurnolL2) : ℝ :=
  ∫ x : ℝ, ‖inner ℂ (reciprocalTail x) (value x)‖

private theorem outer_budget (value : BurnolL2) (a : ℝ) (positive : 0 < a) :
    ‖∫ x in windowᶜ, inner ℂ ((scaled a) x) (value x)‖ ≤ tailBudget value := by
  have scale := ae_restrict_of_ae (s := windowᶜ) (scaled_raw a positive)
  have baseRead := ae_restrict_of_ae (s := windowᶜ)
    (burnolSourceScaleReciprocalPrimitive_coeFn 4 (by norm_num))
  have outside : ∀ᵐ x ∂volume.restrict windowᶜ, x ∈ windowᶜ :=
    ae_restrict_mem (measurableSet_symmetricInterval q).compl
  have paid : ∀ᵐ x ∂volume.restrict windowᶜ,
      ‖inner ℂ ((scaled a) x) (value x)‖ ≤ ‖inner ℂ (reciprocalTail x) (value x)‖ := by
    filter_upwards [scale,baseRead,outside] with x actual kernel away
    have radius : q < |x| := lt_of_not_ge (fun inside => away (abs_le.mp inside))
    have nonzero : x ≠ 0 := by
      intro zero
      rw [zero,abs_zero] at radius
      norm_num [burnolUnscaledCommonGapRadius] at radius
    have absPositive := abs_pos.mpr nonzero
    have read : |x|⁻¹ < 4 := by
      rw [inv_eq_one_div,div_lt_iff₀ absPositive]
      norm_num [burnolUnscaledCommonGapRadius] at radius
      linarith
    change reciprocalTail x = _ at kernel
    rw [if_pos read] at kernel
    simp only [RCLike.inner_apply,starRingEnd_apply,norm_mul,norm_star,actual,kernel,
      norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_abs,abs_of_pos positive]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have bound := burnolUnitCountingPrimitive_bound (a*x) (mul_ne_zero positive.ne' nonzero)
    calc
      a * ‖Hraw (a*x)‖ ≤ a * |a*x|⁻¹ := mul_le_mul_of_nonneg_left bound positive.le
      _ = |x|⁻¹ := by rw [abs_mul,abs_of_pos positive]; field_simp
  have first := (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (scaled a) value).norm
  have second := (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) reciprocalTail value).norm
  calc
    _ ≤ ∫ x in windowᶜ, ‖inner ℂ ((scaled a) x) (value x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in windowᶜ, ‖inner ℂ (reciprocalTail x) (value x)‖ :=
      integral_mono_ae first.integrableOn second.integrableOn paid
    _ ≤ tailBudget value := by
      unfold tailBudget
      rw [← integral_add_compl (measurableSet_symmetricInterval q) second]
      exact le_add_of_nonneg_left (integral_nonneg fun _ => norm_nonneg _)

private def gapMass (a : ℝ) : ℝ := ∫ x in -(a*q)..a*q, loss x

private theorem gap_mass_nonnegative (a : ℝ) (positive : 0 < a) : 0 ≤ gapMass a := by
  have radius : 0 ≤ a*q := mul_nonneg positive.le (by norm_num [burnolUnscaledCommonGapRadius])
  exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => norm_nonneg (Hraw x))

private theorem gap_pair (value : BurnolL2) (b : ℂ)
    (gap : burnolQuarterRestriction value = b • intervalConstant q)
    (a : ℝ) (positive : 0 < a) :
    (∫ x in window, inner ℂ ((scaled a) x) (value x)) = -(b*(gapMass a : ℂ)) := by
  have read := gap_read value b gap
  have scaledRead := ae_restrict_of_ae (s := window) (scaled_raw a positive)
  have integrand : (fun x => inner ℂ ((scaled a) x) (value x)) =ᵐ[volume.restrict window]
      (fun x => (-(a:ℂ)*b)*(loss (a*x):ℂ)) := by
    filter_upwards [read,scaledRead] with x valueAt scaledAt
    have realStar : star (a:ℂ) = (a:ℂ) := Complex.conj_ofReal a
    rw [RCLike.inner_apply,starRingEnd_apply,scaledAt,star_mul,realStar,raw_conj,valueAt]
    ring
  have interval : (∫ x in window, loss (a*x)) = ∫ x in -q..q, loss (a*x) := by
    rw [intervalIntegral.integral_of_le (by norm_num [burnolUnscaledCommonGapRadius])]
    exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm
  rw [integral_congr_ae integrand,integral_const_mul,integral_complex_ofReal,interval,
    intervalIntegral.integral_comp_mul_left (fun x => loss x) positive.ne']
  change -(a:ℂ)*b*((a⁻¹*(∫ x in a * (-q)..a*q, loss x) : ℝ):ℂ) = _
  rw [mul_neg]
  push_cast
  unfold gapMass
  have nonzero : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  field_simp [nonzero]

private def price (a : ℝ) (value : BurnolL2) : ℂ := inner ℂ (scaled a) value

private theorem gap_budget (value : BurnolL2) (b : ℂ)
    (gap : burnolQuarterRestriction value = b • intervalConstant q)
    (a : ℝ) (positive : 0 < a) :
    ‖b‖ * gapMass a ≤ ‖price a value‖ + tailBudget value := by
  let outer := ∫ x in windowᶜ, inner ℂ ((scaled a) x) (value x)
  have whole : -(b*(gapMass a : ℂ))+outer = price a value := by
    rw [← gap_pair value b gap a positive]
    exact integral_add_compl (measurableSet_symmetricInterval q) (MeasureTheory.L2.integrable_inner _ _)
  have gapEq : -(b*(gapMass a : ℂ)) = price a value - outer := eq_sub_of_add_eq whole
  have paid : ‖-(b*(gapMass a : ℂ))‖ ≤ ‖price a value‖ + ‖outer‖ := by
    rw [gapEq]
    exact norm_sub_le _ _
  rw [norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (gap_mass_nonnegative a positive)] at paid
  exact paid.trans (add_le_add_right (outer_budget value a positive) _)

private theorem price_step (value : BurnolL2)
    (silent : ∀ h : ℝ, 0 ≤ h → E (D (-h) value) = 0) (a : ℝ) (positive : 1 ≤ a) :
    price (2*a) value = price a value := by
  have apos : 0 < a := zero_lt_one.trans_le positive
  obtain ⟨test,inside,read⟩ := Submodule.mem_map.mp
    (burnolReciprocalStepNativeWave_closedPa 1 2 (by norm_num) (by norm_num))
  have zero : inner ℂ W (D (-(Real.log a)) value) = 0 := by
    rw [← read]
    have paid := (OriginalKCombCofinalPaAction.wholePa_normal_read (D (-(Real.log a)) value) test inside).symm
    rw [silent _ (Real.log_nonneg positive),inner_zero_right] at paid
    exact paid
  have moved := (D (Real.log a)).inner_map_map W (D (-(Real.log a)) value)
  rw [burnolMultiplicativeDilation_neg_eq_symm,LinearIsometryEquiv.apply_symm_apply] at moved
  rw [← burnolMultiplicativeDilation_neg_eq_symm] at moved
  have atOne : scaled 1 = H := by
    simp only [scaled,burnolSourceScalePrimitive,Real.sqrt_one,Real.log_one,
      burnolMultiplicativeDilation_zero,one_smul]
  have two : scaled (2*a) = Real.sqrt a • D (Real.log a) (scaled 2) := by
    unfold scaled burnolSourceScalePrimitive
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Real.log_mul (by norm_num : (2:ℝ)≠0) apos.ne']
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,smul_smul,
      burnolMultiplicativeDilation_add]
    rw [RCLike.ofReal_mul,mul_comm (RCLike.ofReal (K := ℂ) (Real.sqrt 2)),add_comm (Real.log 2)]
  have step : scaled (2*a)-scaled a = Real.sqrt a • D (Real.log a) W := by
    change scaled (2*a)-scaled a = Real.sqrt a • D (Real.log a) (scaled 2-scaled 1)
    rw [two,atOne,map_sub,smul_sub]
    rfl
  apply sub_eq_zero.mp
  unfold price
  rw [← inner_sub_left,step,RCLike.real_smul_eq_coe_smul (K := ℂ),inner_smul_left,moved,zero,mul_zero]

private theorem dyadic_price (value : BurnolL2)
    (silent : ∀ h : ℝ, 0 ≤ h → E (D (-h) value) = 0) (n : Nat) :
    price ((2:ℝ)^n) value = price 1 value := by
  induction n with
  | zero => simp only [pow_zero]
  | succ n previous =>
    rw [pow_succ',price_step value silent ((2:ℝ)^n) (one_le_pow₀ (by norm_num)),previous]

private theorem dyadic_mass (n : Nat) : (n:ℝ)*Real.log 2/4 ≤ gapMass ((2:ℝ)^(n+2)) := by
  have address : (2:ℝ)^(n+2)*q = (2:ℝ)^n := by
    rw [pow_add]
    norm_num [burnolUnscaledCommonGapRadius]; ring
  have nonnegative : 0 ≤ (2:ℝ)^n := by positivity
  have lower := harmonic_mass (2^n)
  simp only [Nat.cast_pow,Nat.cast_ofNat] at lower
  have logBound := log_add_one_le_harmonic (2^n)
  rw [Nat.cast_add,Nat.cast_one] at logBound
  have logMono : (n:ℝ)*Real.log 2 ≤ Real.log (((2^n:Nat):ℝ)+1) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have full : (∫ x in (0:ℝ)..(2:ℝ)^n, loss x) ≤ gapMass ((2:ℝ)^(n+2)) := by
    unfold gapMass
    rw [address,← intervalIntegral.integral_add_adjacent_intervals
      (loss_integrable (-((2:ℝ)^n)) 0) (loss_integrable 0 ((2:ℝ)^n))]
    exact le_add_of_nonneg_left (intervalIntegral.integral_nonneg (by linarith)
      (fun x _ => norm_nonneg (Hraw x)))
  exact (div_le_div_of_nonneg_right (logMono.trans logBound) (by norm_num)).trans (lower.trans full)

/-- Any actual inward Pa-silent field has zero original position-gap constant. -/
theorem gap_zero_of_inward_silence (value : BurnolL2) (gap : value ∈ locallyConstantFace q)
    (silent : ∀ h : ℝ, 0 ≤ h → E (D (-h) value) = 0) :
    burnolQuarterRestriction value = 0 := by
  obtain ⟨b,read⟩ := mem_locallyConstantFace_iff_exists.mp gap
  have actual : burnolQuarterRestriction value = b • intervalConstant q := read.symm
  suffices gone : b = 0 by
    refine actual.trans ?_
    rw [gone]
    exact zero_smul ℂ (intervalConstant q)
  by_contra live
  let C := ‖price 1 value‖ + tailBudget value
  have rate : 0 < ‖b‖*Real.log 2 := mul_pos (norm_pos_iff.mpr live) (Real.log_pos (by norm_num))
  obtain ⟨n,late⟩ := exists_nat_gt (4*C/(‖b‖*Real.log 2))
  have strict := (div_lt_iff₀ rate).mp late
  have bound := gap_budget value b actual ((2:ℝ)^(n+2)) (by positivity)
  rw [dyadic_price value silent] at bound
  have lower := (mul_le_mul_of_nonneg_left (dyadic_mass n) (norm_nonneg b)).trans bound
  change ‖b‖*((n:ℝ)*Real.log 2/4) ≤ C at lower
  nlinarith

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "U" => NativeReturnImpulse.unit observation half
local notation "R" => burnolDirectRightResolventCLM c

include nontrivial in
private theorem unit_gap : U ∈ locallyConstantFace q := by
  let born := burnolZeroOwnedUnitTailState observation nontrivial half.down
  have input : burnolUnitTailResponse c 4 ∈ locallyConstantFace q := born.property.1.1
  have picked := projected_source (burnolUnitTailResponse c 4)
  obtain ⟨p,_,read⟩ := Submodule.mem_map.mp picked
  have projected : (E (burnolUnitTailResponse c 4) : BurnolL2) ∈ locallyConstantFace q := read ▸ p.property.1.1
  exact (locallyConstantFace q).sub_mem input projected

/-- Original cofinal silence forces zero original quarter mean of the same injected residual. -/
theorem literal_silence_forces_gap_zero (cutoff : Nat)
    (silent : ∀ ordinal ≥ cutoff, ReentryDifferenceClock.fee observation nontrivial half depth ordinal = 0) :
    burnolQuarterRestriction U = 0 := by
  have impulse := (NativeReturnImpulse.literal_tail_silence_iff observation nontrivial half depth cutoff).1 silent
  have full := (NativeReturnImpulse.impulse_silence_iff_native observation nontrivial half).1 impulse
  apply gap_zero_of_inward_silence U (unit_gap observation nontrivial half)
  intro h nonnegative
  rcases nonnegative.eq_or_lt with zero | positive
  · rw [← zero,neg_zero,burnolMultiplicativeDilation_zero]
    exact unit_invisible observation half
  · have paid := DilationFromPowers.observed_inward_zero E c U (fun n => full (n+1))
      (2*h) (by linarith)
    rwa [show -(2*h)/2 = -h by ring] at paid

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.CountedGapVisibility
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
