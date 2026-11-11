import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Even
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Counting

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ComplementMoment OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Counting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Even
open scoped Topology InnerProductSpace ContDiff ENNReal
attribute [local instance 1100] NormedSpace.complexToReal
open private constant_moment from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ComplementMoment
open private sawtooth_bound from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail
local notation "q"=>(1/4:ℝ)
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "S"=>burnolMeanZeroTruncatedFourier
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def smoothRaw (w:ℂ) (below:w.re<1) (x:ℝ):ℂ:=
  correctionRaw w below x-(1/2:ℂ)*rawMean (powerRaw w)

theorem actual_smooth_contDiff (w:ℂ) (below:w.re<1):ContDiff ℝ ∞ (smoothRaw w below):=by
  exact ((actual_return_contDiff (firstSource w below)).add
    (actual_return_contDiff (S (correction w below)))).sub contDiff_const

private theorem smooth_bounds (w:ℂ) (below:w.re<1):
    ∃L B:ℝ,0≤L∧0≤B∧
      (∀x∈Icc (0:ℝ) q,∀y∈Icc (0:ℝ) q,‖smoothRaw w below y-smoothRaw w below x‖≤L*‖y-x‖)∧
      (∀x∈Icc (0:ℝ) q,‖smoothRaw w below x‖≤B):=by
  have regular:=actual_smooth_contDiff w below
  obtain ⟨L,slopeBound⟩:=isCompact_Icc.exists_bound_of_continuousOn
    (regular.continuous_deriv (by simp)).continuousOn
  obtain ⟨B,valueBound⟩:=isCompact_Icc.exists_bound_of_continuousOn regular.continuous.continuousOn
  refine ⟨max 0 L,max 0 B,le_max_left _ _,le_max_left _ _,?_,fun x hx=>(valueBound x hx).trans (le_max_right _ _)⟩
  intro x hx y hy
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _=>((regular.differentiable (by simp)) t).hasDerivAt.hasDerivWithinAt)
    (fun t ht=>(slopeBound t ht).trans (le_max_right _ _)) (convex_Icc _ _) hx hy

private theorem positive_split (w:ℂ) (below:w.re<1) (x:ℝ) (positive:0<x):
    dualRaw w below x=(1/2:ℂ)*(x:ℂ)^(-star w)+smoothRaw w below x:=by
  simp only [dualRaw,seedRaw,powerRaw,smoothRaw,abs_of_pos positive]
  ring

private theorem smooth_mass (w:ℂ) (below:w.re<1):
    (1/2:ℂ)*(q:ℂ)^(1-star w)/(1-star w)+∫x:ℝ in (0:ℝ)..q,smoothRaw w below x=0:=by
  have belowStar:(star w).re<1:=by simpa only [star_def,conj_re] using below
  have power:IntervalIntegrable (fun x:ℝ=>(x:ℂ)^(-star w)) volume 0 q:=
    intervalIntegral.intervalIntegrable_cpow' (by simp only [neg_re];linarith)
  have smooth:IntervalIntegrable (smoothRaw w below) volume 0 q:=
    (actual_smooth_contDiff w below).continuous.intervalIntegrable 0 q
  have same:(∫x:ℝ in (0:ℝ)..q,dualRaw w below x)=
      ∫x:ℝ in (0:ℝ)..q,(1/2:ℂ)*(x:ℂ)^(-star w)+smoothRaw w below x:=by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]
    exact setIntegral_congr_fun measurableSet_Ioc (fun x hx=>positive_split w below x hx.1)
  have powerValue:(∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(-star w))=(q:ℂ)^(1-star w)/(1-star w):=by
    simpa only [quarterMoment,logWeight,pow_zero,mul_one] using constant_moment (star w) belowStar
  rw [intervalIntegral.integral_add (power.const_mul _) smooth,intervalIntegral.integral_const_mul,
    powerValue,actual_positive_dual_mean] at same
  linear_combination -same

def floorRaw (w:ℂ) (below:w.re<1) (x:ℝ):ℂ:=
  ∑n∈DualSourceRaw.channels x,dualRaw w below ((n:ℝ)*x)

private theorem positive_count_split (w:ℂ) (below:w.re<1) (x:ℝ) (positive:0<x):
    floorRaw w below x=
      (1/2:ℂ)*(∑n∈Finset.Icc 1 ⌊q/x⌋₊,(((n:ℝ)*x:ℝ):ℂ)^(-star w))+
      ∑n∈Finset.Icc 1 ⌊q/x⌋₊,smoothRaw w below ((n:ℝ)*x):=by
  rw [floorRaw,show DualSourceRaw.channels x=Finset.Icc 1 ⌊q/x⌋₊ by
    simp only [DualSourceRaw.channels,abs_of_pos positive],Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n inside
  have index:(0:ℝ)<n:=by exact_mod_cast (Finset.mem_Icc.mp inside).1
  exact positive_split w below _ (mul_pos index positive)

private theorem count_balance (w:ℂ) (below:w.re<1) (x:ℝ) (positive:0<x):
    floorRaw w below x=(1/2:ℂ)*PowerCountingOrigin.error (star w) x+
      ((∑n∈Finset.Icc 1 ⌊q/x⌋₊,smoothRaw w below ((n:ℝ)*x))-
        (x:ℂ)⁻¹*(∫u:ℝ in (0:ℝ)..q,smoothRaw w below u))+
      (1/2:ℂ)*(q:ℂ)^(-star w)*((1/2:ℂ)-((Int.fract (q/x):ℝ):ℂ)):=by
  rw [positive_count_split w below x positive,PowerCountingOrigin.error]
  have mass:=smooth_mass w below
  linear_combination ((x:ℂ)⁻¹)*mass

/-- The complete grid retains its endpoint sawtooth and its smooth origin half-contact. -/
theorem actual_complete_floor_balance (w:ℂ) (below:w.re<1) (x:ℝ) (positive:0<x):
    floorRaw w below x=(1/2:ℂ)*PowerCountingOrigin.error (star w) x+
      SmoothCountingOrigin.error (smoothRaw w below) x+
      dualRaw w below q*((1/2:ℂ)-((Int.fract (q/x):ℝ):ℂ))-smoothRaw w below 0/2:=by
  rw [count_balance w below x positive,SmoothCountingOrigin.error,
    positive_split w below q (by norm_num)]
  ring

private theorem channel_inside (x:ℝ) (n:ℕ) (inside:n∈DualSourceRaw.channels x):
    (n:ℝ)*x∈Icc (-q) q:=by
  by_cases zero:x=0
  · subst x
    norm_num
  have positive:0 < |x|:=abs_pos.mpr zero
  have top:(n:ℝ)≤q / |x|:=by
    have index:(n:ℝ)≤(⌊q / |x|⌋₊:ℝ):=by exact_mod_cast (Finset.mem_Icc.mp inside).2
    exact index.trans (Nat.floor_le (by positivity))
  have bounded:(n:ℝ)*|x| ≤q:=(le_div_iff₀ positive).mp top
  apply abs_le.mp
  simpa only [abs_mul,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n)] using bounded

theorem actual_floor_even (w:ℂ) (below:w.re<1) (x:ℝ):floorRaw w below (-x)=floorRaw w below x:=by
  rw [floorRaw,floorRaw,show DualSourceRaw.channels (-x)=DualSourceRaw.channels x by simp [DualSourceRaw.channels]]
  apply Finset.sum_congr rfl
  intro n inside
  rw [mul_neg]
  exact actual_dual_even w below _ (channel_inside x n inside)

theorem actual_floor_outer_zero (w:ℂ) (below:w.re<1) (x:ℝ) (outside:q < |x|):floorRaw w below x=0:=by
  have positive:0 < |x|:=lt_trans (by norm_num : (0:ℝ)<q) outside
  have index:⌊q / |x|⌋₊=0:=Nat.floor_eq_zero.mpr ((div_lt_one positive).mpr outside)
  simp only [floorRaw,DualSourceRaw.channels,index,Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ)<1),Finset.sum_empty]

theorem actual_floor_origin (w:ℂ) (below:w.re<1):floorRaw w below 0=0:=by
  simp [floorRaw,DualSourceRaw.channels]

def fullFloorRaw (c:BurnolCompletedMellinCoordinate):ℝ→ℂ:=floorRaw c.value c.belowOne

theorem actual_full_floor_bound (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    ∃C:ℝ,0≤C∧∀x:ℝ,‖fullFloorRaw c x‖≤C:=by
  obtain ⟨L,B,lnonnegative,bnonnegative,lipschitz,bounded⟩:=smooth_bounds c.value c.belowOne
  let C:ℝ:=(1/2:ℝ)*|PowerCountingOrigin.bound (star c.value)| *q+(L*q+B)+
    (1/2:ℝ)*‖(q:ℂ)^(-star c.value)‖
  have nonnegative:0≤C:=by dsimp only [C];positivity
  have positiveS:0<(star c.value).re:=by simp only [star_def,conj_re];linarith [c.rightHalf]
  have belowS:(star c.value).re<1:=by simpa only [star_def,conj_re] using c.belowOne
  have sourceZero:riemannZeta (star c.value)=0:=by
    simpa only [star_def,zero,map_zero] using riemannZeta_conj c.value
  have localBound (x:ℝ) (positive:0<x) (small:x≤q):‖floorRaw c.value c.belowOne x‖≤C:=by
    have power:=PowerCountingOrigin.error_bound (star c.value) positiveS belowS sourceZero x positive
    have regular:=RegularQuadrature.quadrature_bound _ (actual_smooth_contDiff c.value c.belowOne).continuous.continuousOn
      L B lnonnegative bnonnegative lipschitz bounded x positive
    have powerBound:‖PowerCountingOrigin.error (star c.value) x‖≤|PowerCountingOrigin.bound (star c.value)| *q:=
      power.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) positive.le).trans
        (mul_le_mul_of_nonneg_left small (abs_nonneg _)))
    rw [count_balance c.value c.belowOne x positive]
    calc
      _≤‖(1/2:ℂ)*PowerCountingOrigin.error (star c.value) x‖+
          ‖(∑n∈Finset.Icc 1 ⌊q/x⌋₊,smoothRaw c.value c.belowOne ((n:ℝ)*x))-
            (x:ℂ)⁻¹*(∫u:ℝ in (0:ℝ)..q,smoothRaw c.value c.belowOne u)‖+
          ‖(1/2:ℂ)*(q:ℂ)^(-star c.value)*((1/2:ℂ)-((Int.fract (q/x):ℝ):ℂ))‖:=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _≤C:=by
        simp only [norm_mul,norm_div,norm_one,Complex.norm_ofNat] at *
        dsimp only [C]
        nlinarith [sawtooth_bound x,mul_le_mul_of_nonneg_left powerBound (by norm_num : (0:ℝ)≤1/2),
          mul_le_mul_of_nonneg_left (sawtooth_bound x) (by positivity : 0≤(1/2:ℝ)*‖(q:ℂ)^(-star c.value)‖)]
  refine ⟨C,nonnegative,fun x=>?_⟩
  by_cases outside:q < |x|
  · rw [fullFloorRaw,actual_floor_outer_zero _ _ x outside,norm_zero]
    exact nonnegative
  have small:|x| ≤q:=le_of_not_gt outside
  by_cases positive:0<x
  · exact localBound x positive (by rwa [abs_of_pos positive] at small)
  by_cases atZero:x=0
  · rw [atZero,fullFloorRaw,actual_floor_origin,norm_zero]
    exact nonnegative
  have negative:x<0:=lt_of_le_of_ne (le_of_not_gt positive) atZero
  rw [fullFloorRaw,←actual_floor_even c.value c.belowOne x]
  exact localBound (-x) (neg_pos.mpr negative) (by rwa [abs_of_neg negative] at small)

private theorem division_read (w:ℂ) (below:w.re<1):
    (fun x:ℝ=>(dualCounting w below:ℝ→ℂ) x/((|x|:ℝ):ℂ))=ᵐ[volume]floorRaw w below:=by
  filter_upwards [actual_dual_counting_raw w below,volume.ae_ne (0:ℝ)] with x raw nonzero
  rw [raw,arithmeticRaw,floorRaw]
  field_simp [Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  ring

theorem actual_full_floor_memLp (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    MemLp (fullFloorRaw c) 2 volume:=by
  have denominator:Measurable (fun x:ℝ=>(((|x|:ℝ):ℂ))⁻¹):=
    ((Complex.continuous_ofReal.comp continuous_abs).measurable).inv
  have quotient:AEStronglyMeasurable
      (fun x:ℝ=>(dualCounting c.value c.belowOne:ℝ→ℂ) x/((|x|:ℝ):ℂ)) volume:=by
    simp only [div_eq_mul_inv]
    exact (Lp.aestronglyMeasurable (dualCounting c.value c.belowOne)).mul denominator.aestronglyMeasurable
  have measurable:AEStronglyMeasurable (fullFloorRaw c) volume:=
    quotient.congr (division_read c.value c.belowOne)
  obtain ⟨C,_,bound⟩:=actual_full_floor_bound c zero
  have localSource:MemLp (fullFloorRaw c) 2 μq:=
    MemLp.of_bound measurable.restrict C (Eventually.of_forall bound)
  have allSource:MemLp ((symmetricInterval q).indicator (fullFloorRaw c)) 2 volume:=
    (memLp_indicator_iff_restrict (measurableSet_symmetricInterval q)).mpr localSource
  have same:(symmetricInterval q).indicator (fullFloorRaw c)=fullFloorRaw c:=by
    funext x
    by_cases inside:x∈symmetricInterval q
    · exact indicator_of_mem inside _
    · rw [indicator_of_notMem inside]
      exact (actual_floor_outer_zero c.value c.belowOne x
        (lt_of_not_ge (fun bounded=>inside (abs_le.mp bounded)))).symm
  rwa [same] at allSource

def fullFloorValue (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):BurnolL2:=
  (actual_full_floor_memLp c zero).toLp (fullFloorRaw c)

theorem actual_full_floor_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (fullFloorValue c zero:ℝ→ℂ)=ᵐ[volume]fullFloorRaw c:=(actual_full_floor_memLp c zero).coeFn_toLp

/-- Division is paid on the same whole field; no finite unrenormalized programme inherits L2 membership. -/
theorem actual_full_floor_division (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (fullFloorValue c zero:ℝ→ℂ)=ᵐ[volume]
      fun x:ℝ=>(dualCounting c.value c.belowOne:ℝ→ℂ) x/((|x|:ℝ):ℂ):=
  (actual_full_floor_raw c zero).trans (division_read c.value c.belowOne).symm

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
