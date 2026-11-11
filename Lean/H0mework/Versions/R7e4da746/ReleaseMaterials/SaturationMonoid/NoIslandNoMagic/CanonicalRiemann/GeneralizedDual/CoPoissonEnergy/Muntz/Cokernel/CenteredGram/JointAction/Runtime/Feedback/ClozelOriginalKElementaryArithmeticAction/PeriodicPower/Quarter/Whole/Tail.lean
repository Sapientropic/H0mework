import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Constant
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PowerCountingOrigin

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Point OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Constant
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting
open scoped Topology InnerProductSpace
attribute [local instance 1100] NormedSpace.complexToReal
open private half_mass from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source
open private box_origin from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Constant
open private forcing_positive_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RegularQuadrature
local notation "q" => (1/4:ℝ)
local notation "box" => burnolRadiusTruncatedFourierRaw q (intervalConstant q)

def regularRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ForcingTail.forcingRemainder c x+aliasRaw c x-jumpCoefficient c*box x-resolvedRaw c 0

def regularSlope (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  RegularQuadrature.forcingSlope c x+aliasSlope c x-
    jumpCoefficient c*Constructor.fourierDerivative (fun _:ℝ=>(1:ℂ)) x

private theorem box_read : box=Constructor.fourierRaw (fun _:ℝ=>(1:ℂ)) := by
  rw [←Constructor.fourierRaw_state]
  exact Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q)

theorem actual_regular_derivative (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (inside : x∈Icc (0:ℝ) q) : HasDerivAt (regularRaw c) (regularSlope c x) x := by
  have generated:=(((RegularQuadrature.forcing_derivative c x inside.1).add
    (actual_alias_derivative c x ⟨by linarith [inside.1],by linarith [inside.2]⟩)).sub
    ((Constructor.fourierRaw_hasDerivAt (fun _:ℝ=>(1:ℂ)) continuous_const x).const_mul
      (jumpCoefficient c))).sub_const (resolvedRaw c 0)
  change HasDerivAt (fun y=>ForcingTail.forcingRemainder c y+aliasRaw c y-
    jumpCoefficient c*box y-resolvedRaw c 0) (regularSlope c x) x
  rw [box_read]
  simpa only [regularSlope,Pi.add_apply,Pi.sub_apply] using generated

theorem actual_regular_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (regularRaw c) (Icc (0:ℝ) q) :=
  fun x hx=>(actual_regular_derivative c x hx).continuousAt.continuousWithinAt

theorem actual_regular_slope_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (regularSlope c) (Icc (0:ℝ) q) := by
  exact ((RegularQuadrature.forcing_slope_continuous c).add
    ((actual_alias_slope_continuous c).mono (by intro x hx;constructor <;> linarith [hx.1,hx.2]))).sub
      (continuousOn_const.mul (Constructor.fourierDerivative_continuous _ continuous_const).continuousOn)

theorem actual_regular_bounds (c : BurnolCompletedMellinCoordinate) :
    ∃L B:ℝ,0≤L ∧ 0≤B ∧
      (∀x∈Icc (0:ℝ) q,∀y∈Icc (0:ℝ) q,‖regularRaw c y-regularRaw c x‖≤L*‖y-x‖) ∧
      (∀x∈Icc (0:ℝ) q,‖regularRaw c x‖≤B) := by
  obtain ⟨L,slopeBound⟩:=isCompact_Icc.exists_bound_of_continuousOn (actual_regular_slope_continuous c)
  obtain ⟨B,valueBound⟩:=isCompact_Icc.exists_bound_of_continuousOn (actual_regular_continuous c)
  refine ⟨max 0 L,max 0 B,le_max_left _ _,le_max_left _ _,?_,fun x hx=>(valueBound x hx).trans (le_max_right _ _)⟩
  intro x hx y hy
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht=>(actual_regular_derivative c t ht).hasDerivWithinAt)
    (fun t ht=>(slopeBound t ht).trans (le_max_right _ _)) (convex_Icc _ _) hx hy

theorem actual_periodic_split (c : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    periodicRaw c x=ForcingPrimitive.leadingCoefficient c*(x:ℂ)^(-(1-star c.value))+regularRaw c x := by
  have original:=forcing_positive_read c x positive
  rw [show -(1-star c.value)=star c.value-1 by ring]
  unfold periodicRaw resolvedFourierRaw regularRaw
  linear_combination original

theorem actual_regular_origin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    regularRaw c 0=0 := by
  have selected:riemannZeta (star c.value)=0 := by
    simpa only [star_def,zero,map_zero] using riemannZeta_conj c.value
  rw [regularRaw,RegularQuadrature.forcing_zero,actual_alias_origin_constant,box_origin,selected]
  ring

theorem actual_regular_endpoint (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    ForcingPrimitive.leadingCoefficient c*(q:ℂ)^(-(1-star c.value))+regularRaw c q=0 := by
  rw [←actual_periodic_split c q (by norm_num),actual_original_periodic_zero_quarter c zero]

private theorem whole_mean (c : BurnolCompletedMellinCoordinate) :
    quarterMean c/4=∫u:ℝ in (0:ℝ)..q,periodicRaw c u := by
  rw [←half_mass c]
  have cutoff:EqOn (quarterRaw c) ((Ioc (0:ℝ) q).indicator (periodicRaw c)) (Ioi 0) := by
    intro x positive
    by_cases inside:x≤q
    · have positiveX:0<x:=positive
      rw [quarterRaw,indicator_of_mem (show x∈symmetricInterval q from ⟨by linarith,inside⟩),
        indicator_of_mem (show x∈Ioc (0:ℝ) q from ⟨positive,inside⟩)]
    · rw [quarterRaw,indicator_of_notMem (show x∉symmetricInterval q from fun member=>inside member.2),
        indicator_of_notMem (show x∉Ioc (0:ℝ) q from fun member=>inside member.2)]
  rw [setIntegral_congr_fun measurableSet_Ioi cutoff,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr Ioc_subset_Ioi_self,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]

theorem actual_mean_split (c : BurnolCompletedMellinCoordinate) :
    quarterMean c/4=ForcingPrimitive.leadingCoefficient c*(q:ℂ)^(star c.value)/(star c.value)+
      ∫u:ℝ in (0:ℝ)..q,regularRaw c u := by
  have positive:0<(star c.value).re := by simp only [star_def,conj_re];linarith [c.rightHalf]
  have exponent: -1 < (-(1-star c.value)).re := by
    simp only [neg_re,sub_re,one_re,star_def,conj_re]
    linarith [c.rightHalf]
  have power:IntervalIntegrable (fun x:ℝ=>(x:ℂ)^(-(1-star c.value))) volume 0 q :=
    intervalIntegral.intervalIntegrable_cpow' exponent
  have regular:IntervalIntegrable (regularRaw c) volume 0 q :=
    (actual_regular_continuous c).intervalIntegrable_of_Icc (by norm_num)
  rw [whole_mean]
  have same:(∫u:ℝ in (0:ℝ)..q,periodicRaw c u)=
      ∫u:ℝ in (0:ℝ)..q,ForcingPrimitive.leadingCoefficient c*(u:ℂ)^(-(1-star c.value))+regularRaw c u := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]
    exact setIntegral_congr_fun measurableSet_Ioc (fun u hu=>actual_periodic_split c u hu.1)
  rw [same,intervalIntegral.integral_add (power.const_mul _) regular,intervalIntegral.integral_const_mul,
    integral_cpow (Or.inl exponent),show -(1-star c.value)+1=star c.value by ring,
    Complex.ofReal_zero,Complex.zero_cpow (ne_of_apply_ne Complex.re positive.ne'),sub_zero]
  ring

private theorem inverse_count (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (delta : ℝ) (positive : 0<delta) :
    wholeCountedRaw c delta⁻¹=(delta:ℂ)*
      (∑n∈Finset.Icc 1 ⌊q/delta⌋₊,periodicRaw c ((n:ℝ)*delta))-quarterMean c/4 := by
  rw [actual_positive_floor c zero delta⁻¹ (inv_pos.mpr positive),Complex.ofReal_inv,inv_inv]
  congr 2
  rw [←Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,div_eq_mul_inv]
  simp [add_comm]

/-- The two original zero occurrences remove both the q sawtooth and the regular half-head. -/
theorem actual_complete_count_error (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (delta : ℝ) (positive : 0<delta) :
    wholeCountedRaw c delta⁻¹=(delta:ℂ)*
      (ForcingPrimitive.leadingCoefficient c*PowerCountingOrigin.error (1-star c.value) delta+
        SmoothCountingOrigin.error (regularRaw c) delta) := by
  have sumSplit:(∑n∈Finset.Icc 1 ⌊q/delta⌋₊,periodicRaw c ((n:ℝ)*delta))=
      ForcingPrimitive.leadingCoefficient c*(∑n∈Finset.Icc 1 ⌊q/delta⌋₊,
        (((n:ℝ)*delta:ℝ):ℂ)^(-(1-star c.value)))+
      ∑n∈Finset.Icc 1 ⌊q/delta⌋₊,regularRaw c ((n:ℝ)*delta) := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have index:(0:ℝ)<n:=by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact actual_periodic_split c _ (mul_pos index positive)
  rw [inverse_count c zero delta positive,sumSplit,actual_mean_split,
    PowerCountingOrigin.error,SmoothCountingOrigin.error,actual_regular_origin c zero,
    show 1-(1-star c.value)=star c.value by ring]
  have endpoint:=actual_regular_endpoint c zero
  have deltaNe:(delta:ℂ)≠0:=Complex.ofReal_ne_zero.mpr positive.ne'
  have cancel:(delta:ℂ)*(delta:ℂ)⁻¹=1:=mul_inv_cancel₀ deltaNe
  linear_combination (delta:ℂ)*((1/2:ℂ)-((Int.fract (q/delta):ℝ):ℂ))*endpoint+
    (ForcingPrimitive.leadingCoefficient c*(q:ℂ)^(star c.value)/(star c.value)+
      ∫u:ℝ in (0:ℝ)..q,regularRaw c u)*cancel

private theorem reverse_zero (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    riemannZeta (1-star c.value)=0 := by
  have positive:0<(1-star c.value).re := by
    simp only [sub_re,one_re,star_def,conj_re]
    linarith [c.belowOne]
  have notOne:1-star c.value≠1 := by
    intro same
    have realPart:=congrArg Complex.re same
    simp only [sub_re,one_re,star_def,conj_re] at realPart
    linarith [c.rightHalf]
  exact tendsto_nhds_unique (DirichletCoefficient.coefficient_tendsto_riemannZeta _ positive notOne)
    (DirichletCoefficient.original_coefficient_limits c zero).2

private theorem sawtooth_bound (delta : ℝ) :
    ‖(1/2:ℂ)-((Int.fract (q/delta):ℝ):ℂ)‖≤1 := by
  have read:(1/2:ℂ)-((Int.fract (q/delta):ℝ):ℂ)=((1/2-Int.fract (q/delta):ℝ):ℂ):=by push_cast;rfl
  rw [read,Complex.norm_real,Real.norm_eq_abs,abs_le]
  constructor <;> linarith [Int.fract_nonneg (q/delta),Int.fract_lt_one (q/delta)]

private theorem smooth_error_bound (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (L B : ℝ) (lnonnegative : 0≤L) (bnonnegative : 0≤B)
    (lipschitz : ∀x∈Icc (0:ℝ) q,∀y∈Icc (0:ℝ) q,‖regularRaw c y-regularRaw c x‖≤L*‖y-x‖)
    (bounded : ∀x∈Icc (0:ℝ) q,‖regularRaw c x‖≤B) (delta : ℝ) (positive : 0<delta) :
    ‖SmoothCountingOrigin.error (regularRaw c) delta‖≤L*q+2*B := by
  have quadrature:=RegularQuadrature.quadrature_bound _ (actual_regular_continuous c)
    L B lnonnegative bnonnegative lipschitz bounded delta positive
  rw [SmoothCountingOrigin.error,actual_regular_origin c zero,zero_div,add_zero]
  apply (norm_sub_le _ _).trans
  have last:‖regularRaw c q*((1/2:ℂ)-((Int.fract (q/delta):ℝ):ℂ))‖≤B := by
    rw [norm_mul]
    exact (mul_le_mul (bounded q (by norm_num)) (sawtooth_bound delta) (norm_nonneg _) bnonnegative).trans_eq (mul_one B)
  exact (add_le_add quadrature last).trans_eq (by ring)

/-- The actual reversal-zero rate controls the whole co-sum, not a clock difference. -/
theorem actual_whole_counted_tail (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    ∃C:ℝ,0≤C ∧ ∀x:ℝ,1≤x→‖wholeCountedRaw c x‖≤C/x := by
  obtain ⟨L,B,lnonnegative,bnonnegative,lipschitz,bounded⟩:=actual_regular_bounds c
  let C:=‖ForcingPrimitive.leadingCoefficient c‖*|PowerCountingOrigin.bound (1-star c.value)|+L*q+2*B
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro x large
  have positiveX:0<x:=lt_of_lt_of_le (by norm_num) large
  have positive:0<x⁻¹:=inv_pos.mpr positiveX
  have small:x⁻¹≤1:=by simpa using (inv_le_one₀ positiveX).mpr large
  have positiveS:0<(1-star c.value).re := by
    simp only [sub_re,one_re,star_def,conj_re]
    linarith [c.belowOne]
  have belowS:(1-star c.value).re<1 := by
    simp only [sub_re,one_re,star_def,conj_re]
    linarith [c.rightHalf]
  have arithmetic:=PowerCountingOrigin.error_bound (1-star c.value) positiveS belowS (reverse_zero c zero) x⁻¹ positive
  have arithmeticBound:‖PowerCountingOrigin.error (1-star c.value) x⁻¹‖≤
      |PowerCountingOrigin.bound (1-star c.value)| :=
    arithmetic.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) positive.le).trans
      (mul_le_of_le_one_right (abs_nonneg _) small))
  have regular:=smooth_error_bound c zero L B lnonnegative bnonnegative lipschitz bounded x⁻¹ positive
  have source:=actual_complete_count_error c zero x⁻¹ positive
  rw [inv_inv] at source
  rw [source,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  calc
    _≤x⁻¹*(‖ForcingPrimitive.leadingCoefficient c‖*
        |PowerCountingOrigin.bound (1-star c.value)|+(L*q+2*B)) := by
      apply mul_le_mul_of_nonneg_left _ positive.le
      exact (norm_add_le _ _).trans (add_le_add
        (by rw [norm_mul];exact mul_le_mul_of_nonneg_left arithmeticBound (norm_nonneg _)) regular)
    _=C/x := by dsimp [C];ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
