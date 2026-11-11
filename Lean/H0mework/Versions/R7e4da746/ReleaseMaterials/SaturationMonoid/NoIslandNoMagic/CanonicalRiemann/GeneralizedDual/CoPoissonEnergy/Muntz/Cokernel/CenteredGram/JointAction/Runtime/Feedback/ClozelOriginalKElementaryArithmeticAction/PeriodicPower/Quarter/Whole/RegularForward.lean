import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ReciprocalMoment

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ReciprocalMoment
open scoped Topology InnerProductSpace
open private source_forward_of_linear_origin reciprocal_integrable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
local notation "q" => (1/4:ℝ)
local notation "r" => OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.regularRaw

def regularLocal (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ := r c (min q |x|)

def regularCompactRaw (c:BurnolCompletedMellinCoordinate):ℝ→ℂ :=
  (Ioo (-q) q).indicator (regularLocal c)

theorem actual_regular_local_continuous (c:BurnolCompletedMellinCoordinate):Continuous (regularLocal c):=by
  apply (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.actual_regular_continuous c).comp_continuous
    (continuous_const.min continuous_abs)
  intro x
  exact ⟨le_min (by norm_num) (abs_nonneg x),min_le_left _ _⟩

theorem actual_regular_measurable (c:BurnolCompletedMellinCoordinate):Measurable (regularCompactRaw c):=
  (actual_regular_local_continuous c).measurable.indicator measurableSet_Ioo

theorem actual_regular_even (c:BurnolCompletedMellinCoordinate) (x:ℝ):
    regularCompactRaw c (-x)=regularCompactRaw c x:=by
  have same:-x∈Ioo (-q) q↔x∈Ioo (-q) q:=by
    simp only [mem_Ioo]
    constructor <;> rintro ⟨left,right⟩ <;> constructor <;> linarith
  simp only [regularCompactRaw,indicator_apply,same,regularLocal,abs_neg]

theorem actual_regular_outer_zero (c:BurnolCompletedMellinCoordinate) (x:ℝ) (outside:q≤|x|):
    regularCompactRaw c x=0:=by
  apply indicator_of_notMem
  intro inside
  exact (not_lt.mpr outside) (abs_lt.mpr inside)

theorem actual_regular_positive_read (c:BurnolCompletedMellinCoordinate) (x:ℝ)
    (positive:0<x) (below:x<q):regularCompactRaw c x=r c x:=by
  rw [regularCompactRaw,indicator_of_mem (show x∈Ioo (-q) q from ⟨by linarith,below⟩),
    regularLocal,abs_of_pos positive,min_eq_right below.le]

theorem actual_regular_origin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    regularCompactRaw c 0=0:=by
  rw [regularCompactRaw,indicator_of_mem (by norm_num : (0:ℝ)∈Ioo (-q) q),
    regularLocal,abs_zero,min_eq_right (by norm_num : (0:ℝ)≤q),
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.actual_regular_origin c zero]

theorem actual_regular_global_growth (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    ∃L:ℝ,0≤L ∧ ∀x:ℝ,‖regularCompactRaw c x‖≤L*|x|:=by
  obtain ⟨L,nonnegative,bound⟩:=actual_regular_linear_bound c zero
  refine ⟨L,nonnegative,?_⟩
  intro x
  by_cases inside:x∈Ioo (-q) q
  · rw [regularCompactRaw,indicator_of_mem inside,regularLocal,
      min_eq_right (abs_lt.mpr inside).le]
    exact bound |x| ⟨abs_nonneg x,(abs_lt.mpr inside).le⟩
  · rw [regularCompactRaw,indicator_of_notMem inside,norm_zero]
    exact mul_nonneg nonnegative (abs_nonneg x)

theorem actual_regular_memLp (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    MemLp (regularCompactRaw c) 2 volume:=by
  obtain ⟨L,nonnegative,growth⟩:=actual_regular_global_growth c zero
  have majorant:MemLp ((Ioo (-q) q).indicator (fun _:ℝ=>(L*q:ℂ))) 2 volume:=
    memLp_indicator_const 2 measurableSet_Ioo _ (Or.inr (by simp))
  apply majorant.mono (actual_regular_measurable c).aestronglyMeasurable
  filter_upwards with x
  by_cases inside:x∈Ioo (-q) q
  · rw [indicator_of_mem inside,←Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0≤L*q)]
    exact (growth x).trans (mul_le_mul_of_nonneg_left (abs_lt.mpr inside).le nonnegative)
  · rw [regularCompactRaw,indicator_of_notMem inside,indicator_of_notMem inside,norm_zero]

def regularSource (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):BurnolL2 :=
  (actual_regular_memLp c zero).toLp (regularCompactRaw c)

theorem actual_regular_source_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (regularSource c zero:ℝ→ℂ)=ᵐ[volume] regularCompactRaw c:=
  (actual_regular_memLp c zero).coeFn_toLp

theorem actual_regular_mean (c:BurnolCompletedMellinCoordinate):
    (∫x:ℝ in Ioi 0,(x:ℂ)⁻¹*regularCompactRaw c x)=regularReciprocalMean c:=by
  have cutoff:EqOn (fun x:ℝ=>(x:ℂ)⁻¹*regularCompactRaw c x)
      ((Ioo (0:ℝ) q).indicator (fun x:ℝ=>(x:ℂ)⁻¹*r c x)) (Ioi 0):=by
    intro x positive
    change 0<x at positive
    dsimp only
    by_cases below:x<q
    · rw [actual_regular_positive_read c x positive below,
        indicator_of_mem (show x∈Ioo (0:ℝ) q from ⟨positive,below⟩)]
    · rw [actual_regular_outer_zero c x (by simpa only [abs_of_pos positive] using le_of_not_gt below),
        mul_zero,indicator_of_notMem (show x∉Ioo (0:ℝ) q from fun inside=>below inside.2)]
  rw [setIntegral_congr_fun measurableSet_Ioi cutoff,integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,inter_eq_left.mpr Ioo_subset_Ioi_self,
    ←integral_Ioc_eq_integral_Ioo,regularReciprocalMean,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]

def regularForwardRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ :=
  burnolInnerGapForward (regularCompactRaw c) x-regularReciprocalMean c

/-- The genuine regular source computes its full forward field, including its own Unit. -/
theorem actual_regular_forward_read (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (test:SchwartzMap ℝ ℂ):
    burnolRemainderSourceRead (regularSource c zero) test=∫x:ℝ,test x*regularForwardRaw c x:=by
  obtain ⟨L,nonnegative,growth⟩:=actual_regular_global_growth c zero
  have native:=source_forward_of_linear_origin (regularSource c zero) (regularCompactRaw c)
    (actual_regular_source_raw c zero) (actual_regular_measurable c) (actual_regular_origin c zero)
    (actual_regular_even c) L nonnegative growth (actual_regular_outer_zero c) test
  simpa only [actual_regular_mean,regularForwardRaw] using native

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
