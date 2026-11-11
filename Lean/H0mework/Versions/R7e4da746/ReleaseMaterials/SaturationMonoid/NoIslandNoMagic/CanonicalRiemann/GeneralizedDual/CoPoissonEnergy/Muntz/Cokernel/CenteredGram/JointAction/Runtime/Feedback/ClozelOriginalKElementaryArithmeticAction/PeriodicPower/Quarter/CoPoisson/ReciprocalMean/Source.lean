import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Constant OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
open scoped Topology ENNReal InnerProductSpace FourierTransform
open private box_source from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Action
open private aliasBound aliasBound_nonnegative aliasBound_read alias_change from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source
open private compact_norm_bound from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
open private bochner_scaled_mellin mellin_source_ae from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource
local notation "q" => (1/4:ℝ)
local notation "box" => burnolRadiusTruncatedFourierRaw q (intervalConstant q)
local notation "F" => fourierL2

private theorem box_lipschitz : ∃ B:ℝ, 0≤B ∧ ∀ x∈symmetricInterval q,
    ‖box x-box 0‖≤B*|x| := by
  have regular : ContinuousOn (Constructor.fourierDerivative (fun _:ℝ=>(1:ℂ))) (symmetricInterval q) := (Constructor.fourierDerivative_continuous (fun _:ℝ=>(1:ℂ)) continuous_const).continuousOn
  obtain ⟨B,bound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s:=symmetricInterval q) regular
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro x inside
  have derivative : ∀ y∈symmetricInterval q, HasDerivWithinAt box
      (Constructor.fourierDerivative (fun _:ℝ=>(1:ℂ)) y) (symmetricInterval q) y := by
    intro y _
    have source:=Constructor.fourierRaw_hasDerivAt (fun _:ℝ=>(1:ℂ)) continuous_const y
    rw [box_source] at source
    exact source.hasDerivWithinAt
  simpa only [sub_zero,Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le derivative
      (fun y hy=>(bound y hy).trans (le_max_right 0 B)) (convex_Icc _ _)
      (by norm_num [symmetricInterval] : (0:ℝ)∈symmetricInterval q) inside

/-- The finite Poisson head pays the reciprocal companion's actual local integrability. -/
theorem actual_companion_linear_bound (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) : ∃ B:ℝ, 0≤B ∧ ∀ x∈symmetricInterval q,
      ‖companionRaw c x‖≤B*|x| := by
  obtain ⟨B,nonnegative,boxBound⟩ := box_lipschitz
  let a:ℂ := (star c.value-1)*jumpCoefficient c
  let M:ℝ := ‖a‖*B+aliasBound c+‖star c.value-1‖*aliasBound c
  have aliasNonnegative:=aliasBound_nonnegative c
  refine ⟨M,by dsimp [M];positivity,?_⟩
  intro x inside
  have head:=actual_original_companion_origin c zero
  have split : companionRaw c x=a*(box x-box 0)+(x:ℂ)*aliasSlope c x-
      (star c.value-1)*(aliasRaw c x-aliasRaw c 0) := by
    unfold companionRaw at head ⊢
    dsimp only [a]
    simp only [Complex.ofReal_zero,zero_mul,add_zero] at head
    linear_combination head
  rw [split]
  calc
    _≤(‖a‖*‖box x-box 0‖+‖(x:ℂ)‖*‖aliasSlope c x‖)+
        ‖star c.value-1‖*‖aliasRaw c x-aliasRaw c 0‖ := by
      simpa only [norm_mul] using
        (norm_sub_le (a*(box x-box 0)+(x:ℂ)*aliasSlope c x)
          ((star c.value-1)*(aliasRaw c x-aliasRaw c 0))).trans
          (add_le_add (norm_add_le (a*(box x-box 0)) ((x:ℂ)*aliasSlope c x)) le_rfl)
    _≤(‖a‖*(B*|x|)+|x| *aliasBound c)+‖star c.value-1‖*(aliasBound c*|x|) := by
      simp only [Complex.norm_real,Real.norm_eq_abs]
      have change:=alias_change c 0 x (by norm_num [symmetricInterval]) inside
      simp only [sub_zero] at change
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (boxBound x inside) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (aliasBound_read c x inside) (abs_nonneg x)))
        (mul_le_mul_of_nonneg_left change (norm_nonneg _))
    _=M*|x| := by dsimp [M];ring

def companionWholeRaw (c:BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  (symmetricInterval q).indicator (companionRaw c)

def companionReciprocalMean (c:BurnolCompletedMellinCoordinate) : ℂ :=
  ∫ x:ℝ in Ioi 0, (x:ℂ)⁻¹*companionWholeRaw c x

private theorem companion_whole_read (c:BurnolCompletedMellinCoordinate) :
    (companion c:ℝ→ℂ)=ᵐ[volume] companionWholeRaw c := by
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (actual_companion_raw c)
  filter_upwards [burnolQuarterZeroExtension_coe (companionQuarter c),localRead] with x extended raw
  change (burnolQuarterZeroExtension (companionQuarter c):ℝ→ℂ) x=_
  rw [extended]
  unfold companionWholeRaw
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,indicator_of_mem inside,raw inside]
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

private theorem companion_whole_bound (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) : ∃ B:ℝ, 0≤B ∧ ∀ x:ℝ,
      ‖companionWholeRaw c x‖≤B*|x| := by
  obtain ⟨B,nonnegative,bound⟩:=actual_companion_linear_bound c zero
  refine ⟨B,nonnegative,?_⟩
  intro x
  unfold companionWholeRaw
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside]
    exact bound x inside
  · rw [indicator_of_notMem inside,norm_zero]
    exact mul_nonneg nonnegative (abs_nonneg x)

theorem actual_companion_mellin_zero (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) :
    HasMellin (companion c:ℝ→ℂ) 0 (companionReciprocalMean c) := by
  obtain ⟨B,nonnegative,bound⟩:=companion_whole_bound c zero
  have weighted : (fun x:ℝ=>(x:ℂ)⁻¹*(companion c:ℝ→ℂ) x)=ᵐ[volume]
      fun x:ℝ=>(x:ℂ)⁻¹*companionWholeRaw c x := by
    filter_upwards [companion_whole_read c] with x actual
    rw [actual]
  have integrable : Integrable (fun x:ℝ=>(x:ℂ)⁻¹*(companion c:ℝ→ℂ) x) := by
    apply (compact_norm_bound B nonnegative).mono'
      (((Complex.measurable_ofReal.comp measurable_id).inv).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable (companion c)))
    filter_upwards [weighted] with x actual
    change ‖(x:ℂ)⁻¹*(companion c:ℝ→ℂ) x‖≤(symmetricInterval q).indicator (fun _:ℝ=>B) x
    rw [actual]
    by_cases inside:x∈symmetricInterval q
    · rw [indicator_of_mem inside,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs]
      by_cases origin:x=0
      · subst x
        simpa using nonnegative
      have positive:0 < |x|:=abs_pos.mpr origin
      calc
        _≤|x|⁻¹*(B*|x|):=mul_le_mul_of_nonneg_left (bound x) (inv_nonneg.mpr positive.le)
        _=B:=by field_simp
    · rw [indicator_of_notMem inside,companionWholeRaw,indicator_of_notMem inside,mul_zero,norm_zero]
  constructor
  · simpa only [MellinConvergent,zero_sub,Complex.cpow_neg_one,smul_eq_mul] using integrable.integrableOn (s:=Ioi 0)
  · simpa only [mellin,zero_sub,Complex.cpow_neg_one,smul_eq_mul,companionReciprocalMean] using
      integral_congr_ae (ae_restrict_of_ae (s:=Ioi 0) weighted)

def drivingOrbit (c:BurnolCompletedMellinCoordinate) (t:ℝ) : BurnolL2 :=
  positiveMellinQuarterRightResolventWeight (star c.value/2) t •
    burnolMultiplicativeDilation (t/2) (companion c)

/-- The original R finite boundary drives the entire wave, before any Unit read. -/
theorem actual_wave_integral (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (nonnegative:0≤h) :
    waveDifference c h=(Complex.exp ((star c.value-1/2)*(h:ℂ))/2) •
      ∫ t:ℝ in Ioc 0 (2*h), drivingOrbit c t := by
  apply fourierL2.injective
  rw [actual_wave_source_boundary c zero]
  have mapped : F (∫ t:ℝ in Ioc 0 (2*h), drivingOrbit c t)=
      ∫ t:ℝ in Ioc 0 (2*h), F (drivingOrbit c t) :=
    (LinearIsometry.integral_comp_comm fourierL2.toLinearIsometry
      (fun t:ℝ=>drivingOrbit c t) (μ:=volume.restrict (Ioc 0 (2*h)))).symm
  rw [map_smul,mapped]
  unfold burnolDirectRightResolventSignedBoundary
  rw [intervalIntegral.integral_of_le (by linarith : (0:ℝ)≤2*h)]
  have rows : ∀ t:ℝ, burnolDirectRightResolventIntegrand (star c.value/2)
      (resolventForcing c) t=(1/2:ℂ) • F (drivingOrbit c t) := by
    intro t
    unfold burnolDirectRightResolventIntegrand resolventForcing drivingOrbit
    rw [map_smul,map_smul,fourierL2_burnolMultiplicativeDilation]
    rw [show -(t/2)= -t/2 by ring]
    module
  simp_rw [rows]
  rw [integral_smul,smul_smul]
  congr 1
  ring

private def unitWeight (c:BurnolCompletedMellinCoordinate) (t:ℝ) : ℂ :=
  Complex.exp (((1-star c.value)/2)*(t:ℂ))

private theorem unitWeight_continuous (c:BurnolCompletedMellinCoordinate) :
    Continuous (unitWeight c) := by unfold unitWeight;fun_prop

private theorem driving_continuous (c:BurnolCompletedMellinCoordinate) :
    Continuous (drivingOrbit c) :=
  (positiveMellinQuarterRightResolventWeight_continuous (star c.value/2)).smul
    ((burnolMultiplicativeDilation_stronglyContinuous (companion c)).comp (by fun_prop))

private theorem actual_integral_mellin_zero (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) :
    HasMellin ((∫t:ℝ in Ioc 0 (2*h),drivingOrbit c t):BurnolL2) 0
      ((∫t:ℝ in Ioc 0 (2*h),unitWeight c t)*companionReciprocalMean c) := by
  let clock:=Ioc (0:ℝ) (2*h)
  let family:ℝ→BurnolL2:=clock.indicator (drivingOrbit c)
  let weight:ℝ→ℂ:=clock.indicator (unitWeight c)
  let scale:ℝ→ℝ:=fun t=>Real.exp (t/2)
  have familyIntegrable : Integrable family :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      (((driving_continuous c).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  have weightIntegrable : Integrable weight :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      (((unitWeight_continuous c).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  have weightMeasurable : Measurable weight :=
    (unitWeight_continuous c).measurable.indicator measurableSet_Ioc
  have reads : ∀ᵐt:ℝ∂volume.restrict (Ioi 0), (family t:ℝ→ℂ)=ᵐ[volume]
      fun x:ℝ=>weight t*(companion c:ℝ→ℂ) (scale t*x) := by
    filter_upwards with t
    by_cases inside:t∈clock
    · dsimp only [family,weight]
      rw [indicator_of_mem inside,indicator_of_mem inside]
      filter_upwards [Lp.coeFn_smul (positiveMellinQuarterRightResolventWeight (star c.value/2) t)
        (burnolMultiplicativeDilation (t/2) (companion c)),
        burnolMultiplicativeDilation_coeFn (t/2) (companion c)] with x scalar dilation
      change (positiveMellinQuarterRightResolventWeight (star c.value/2) t •
        burnolMultiplicativeDilation (t/2) (companion c):BurnolL2) x=_
      rw [scalar,Pi.smul_apply,smul_eq_mul,dilation]
      have price : positiveMellinQuarterRightResolventWeight (star c.value/2) t *
          (Real.exp ((t/2)/2):ℂ)=unitWeight c t := by
        unfold positiveMellinQuarterRightResolventWeight unitWeight
        rw [Complex.ofReal_exp,←Complex.exp_add]
        congr 1
        push_cast
        ring
      dsimp only [scale]
      rw [burnolL2RawNormalizedDilation,←mul_assoc,price]
    · dsimp only [family,weight]
      rw [indicator_of_notMem inside,indicator_of_notMem inside]
      filter_upwards [Lp.coeFn_zero ℂ 2 volume] with x source
      simp only [source,zero_mul,Pi.zero_apply]
  have budget : IntegrableOn (fun t:ℝ=>‖weight t*(scale t:ℂ)^(-(0:ℂ))‖) (Ioi 0) := by
    simpa only [neg_zero,Complex.cpow_zero,mul_one] using weightIntegrable.norm.integrableOn (s:=Ioi 0)
  have native:=bochner_scaled_mellin (companion c) 0 (companionReciprocalMean c)
    family familyIntegrable.integrableOn weight scale weightMeasurable (by dsimp [scale];fun_prop)
    (fun t _=>Real.exp_pos (t/2)) reads (actual_companion_mellin_zero c zero) budget
  have sourceIntegral : (∫t:ℝ in Ioi 0,family t) = ∫t:ℝ in clock,drivingOrbit c t := by
    rw [show family=clock.indicator (drivingOrbit c) from rfl,setIntegral_indicator measurableSet_Ioc]
    have same : Ioi (0:ℝ) ∩ Ioc 0 (2*h)=clock := inter_eq_right.mpr (fun _ ht=>ht.1)
    rw [same]
  have weightIntegral : (∫t:ℝ in Ioi 0,weight t) = ∫t:ℝ in clock,unitWeight c t := by
    rw [show weight=clock.indicator (unitWeight c) from rfl,setIntegral_indicator measurableSet_Ioc]
    have same : Ioi (0:ℝ) ∩ Ioc 0 (2*h)=clock := inter_eq_right.mpr (fun _ ht=>ht.1)
    rw [same]
  simp only [neg_zero,Complex.cpow_zero,mul_one] at native
  rw [sourceIntegral,weightIntegral] at native
  exact native

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
