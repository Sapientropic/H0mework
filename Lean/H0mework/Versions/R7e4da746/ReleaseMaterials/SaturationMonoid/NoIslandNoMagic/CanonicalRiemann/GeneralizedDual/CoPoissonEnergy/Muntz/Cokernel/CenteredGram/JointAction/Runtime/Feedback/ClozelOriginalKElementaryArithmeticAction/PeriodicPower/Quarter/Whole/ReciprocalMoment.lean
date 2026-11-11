import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ReciprocalMoment
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Consumer
open scoped Topology InnerProductSpace
open private box_derivative coefficient_eq_jump from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
local notation "q" => (1/4:ℝ)
local notation "r" => OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.regularRaw
local notation "r'" => OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.regularSlope
local notation "box" => burnolRadiusTruncatedFourierRaw q (intervalConstant q)

def regularReciprocalMean (c:BurnolCompletedMellinCoordinate):ℂ :=
  ∫x:ℝ in (0:ℝ)..q,(x:ℂ)⁻¹*r c x

/-- The original power head has a finite reciprocal part; its pole is retained. -/
def wholeReciprocalFinitePart (c:BurnolCompletedMellinCoordinate):ℂ :=
  ForcingPrimitive.leadingCoefficient c*(q:ℂ)^(star c.value-1)/(star c.value-1)+
    regularReciprocalMean c

theorem actual_regular_linear_bound (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):∃L:ℝ,0≤L ∧ ∀x∈Icc (0:ℝ) q,‖r c x‖≤L*x:=by
  obtain ⟨L,B,nonnegative,_,bound,_⟩:=OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.actual_regular_bounds c
  refine ⟨L,nonnegative,?_⟩
  intro x inside
  have generated:=bound 0 (by norm_num) x inside
  simpa only [OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.actual_regular_origin c zero,sub_zero,
    Real.norm_eq_abs,abs_of_nonneg inside.1] using generated

theorem actual_regular_reciprocal_integrable (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    IntervalIntegrable (fun x:ℝ=>(x:ℂ)⁻¹*r c x) volume 0 q:=by
  obtain ⟨L,nonnegative,bound⟩:=actual_regular_linear_bound c zero
  apply (intervalIntegrable_const (c:=L) (a:=0) (b:=q) (μ:=volume)).mono_fun'
  · have measurable:AEStronglyMeasurable (fun x:ℝ=>(x:ℂ)⁻¹*r c x)
        (volume.restrict (Icc (0:ℝ) q)):=
      ((Complex.measurable_ofReal.comp measurable_id).inv).aestronglyMeasurable.mul
      ((OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.actual_regular_continuous c).aestronglyMeasurable
        measurableSet_Icc)
    exact measurable.mono_set (by simpa only [uIoc_of_le (by norm_num : (0:ℝ)≤q)] using
      (Ioc_subset_Icc_self : Ioc (0:ℝ) q⊆Icc (0:ℝ) q))
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x inside
    have inside':x∈Ioc (0:ℝ) q:=by simpa only [uIoc_of_le (by norm_num : (0:ℝ)≤q)] using inside
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos inside'.1]
    exact (mul_le_mul_of_nonneg_left (bound x ⟨inside'.1.le,inside'.2⟩)
      (inv_nonneg.mpr inside'.1.le)).trans_eq (by field_simp [inside'.1.ne'])

/-- The companion differentiates the same regular remainder, including the Fourier box. -/
theorem actual_regular_euler (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x):
    (x:ℂ)*r' c x-(star c.value-1)*r c x=companionRaw c x:=by
  have boxSource:=Constructor.fourierRaw_hasDerivAt (fun _:ℝ=>(1:ℂ)) continuous_const x
  have boxRead:Constructor.fourierRaw (fun _:ℝ=>(1:ℂ))=box:=by
    rw [←Constructor.fourierRaw_state]
    exact Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q).symm
  rw [boxRead] at boxSource
  have same:=boxSource.unique (box_derivative x positive.ne')
  unfold OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.regularRaw OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.regularSlope
    RegularQuadrature.forcingSlope companionRaw
  rw [same,coefficient_eq_jump]
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  ring

private theorem companion_mean_interval (c:BurnolCompletedMellinCoordinate):
    companionReciprocalMean c=∫x:ℝ in (0:ℝ)..q,(x:ℂ)⁻¹*companionRaw c x:=by
  unfold companionReciprocalMean
  have cutoff:EqOn (fun x:ℝ=>(x:ℂ)⁻¹*companionWholeRaw c x)
      ((Ioc (0:ℝ) q).indicator (fun x:ℝ=>(x:ℂ)⁻¹*companionRaw c x)) (Ioi 0):=by
    intro x positive
    change 0<x at positive
    dsimp only
    unfold companionWholeRaw
    by_cases inside:x≤q
    · rw [indicator_of_mem (show x∈symmetricInterval q from ⟨by linarith,inside⟩),
        indicator_of_mem (show x∈Ioc (0:ℝ) q from ⟨positive,inside⟩)]
    · rw [indicator_of_notMem (show x∉symmetricInterval q from fun member=>inside member.2),
        indicator_of_notMem (show x∉Ioc (0:ℝ) q from fun member=>inside member.2),mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi cutoff,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr Ioc_subset_Ioi_self,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]

/-- The complete companion moment generates Whole's reciprocal finite part. -/
theorem actual_whole_reciprocal_finite_part (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    companionReciprocalMean c=(1-star c.value)*wholeReciprocalFinitePart c:=by
  have slopeIntegrable:IntervalIntegrable (r' c) volume 0 q:=
    (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.actual_regular_slope_continuous c).intervalIntegrable_of_Icc
      (by norm_num)
  have reciprocalIntegrable:=actual_regular_reciprocal_integrable c zero
  have slopeIntegral:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f:=r c) (f':=r' c)
    (fun x hx=>OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.actual_regular_derivative c x
      (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤q)] using hx)) slopeIntegrable
  rw [OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.actual_regular_origin c zero,sub_zero] at slopeIntegral
  have same:(∫x:ℝ in (0:ℝ)..q,(x:ℂ)⁻¹*companionRaw c x)=
      ∫x:ℝ in (0:ℝ)..q,r' c x-(star c.value-1)*((x:ℂ)⁻¹*r c x):=by
    apply intervalIntegral.integral_congr_uIoo
    intro x inside
    have positive:0<x:=(by simpa only [uIoo_of_le (by norm_num : (0:ℝ)≤q)] using inside : x∈Ioo (0:ℝ) q).1
    dsimp only
    rw [←actual_regular_euler c x positive]
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  have endpoint:=OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.actual_regular_endpoint c zero
  rw [show -(1-star c.value)=star c.value-1 by ring] at endpoint
  have nonzero:(star c.value-1:ℂ)≠0:=by
    intro same
    have real:=congrArg Complex.re same
    simp only [sub_re,star_def,conj_re,one_re,zero_re] at real
    linarith [c.belowOne]
  rw [companion_mean_interval,same,intervalIntegral.integral_sub slopeIntegrable
    (reciprocalIntegrable.const_mul _),intervalIntegral.integral_const_mul,slopeIntegral]
  unfold wholeReciprocalFinitePart regularReciprocalMean
  field_simp [nonzero]
  linear_combination (star c.value-1)*endpoint

theorem actual_direct_unit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h):
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward.directMean c h=
      ((Real.exp (h/2):ℂ)-Complex.exp ((star c.value-1/2)*(h:ℂ)))*
        wholeReciprocalFinitePart c:=by
  rw [actual_direct_mean c zero h nonnegative,actual_whole_reciprocal_finite_part c zero]
  have nonzero:(1-star c.value:ℂ)≠0:=by
    intro same
    have real:=congrArg Complex.re same
    simp only [sub_re,star_def,conj_re,one_re,zero_re] at real
    linarith [c.belowOne]
  field_simp [nonzero]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ReciprocalMoment
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
