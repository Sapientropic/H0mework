import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCenteredMobiusRSource.UnitTailActionSource
import H0mework.Versions.R7e4da746.Arithmetic.MellinProjection.GapTailDilation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactAdjointRSource.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.AmbientBPriceSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.UnitMellin.ResonantLogTailSource
open Complex MeasureTheory Set Filter BurnolPhysicalState OriginalPaPhysicalGreen
open scoped InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
namespace Native
export OriginalKCenteredMobiusRSource.UnitTailActionSource
  (nativeUnitMuSource nativeUnitMuRaw native_unit_source_zero native_unit_source_profile native_unit_source_action)
end Native
open private evenPart_left from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.AmbientBPriceSource
open private realExp_cpow_halfDensity from
  H0mework.Versions.R7e4da746.Arithmetic.MellinProjection.GapTailDilation
open private conjugate_volterra_quarter from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.HQuarterSource
open private mean_constant from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source
open OriginalRieszFinitePairing.CoPoisson.Ward

private def tail (c:BurnolCompletedMellinCoordinate) (radius:ℝ) (positive:0<radius):BurnolL2:=
  burnolRadiusMellinTailKernelL2 radius positive c.value c.rightHalf

private theorem native_even_tail (c:BurnolCompletedMellinCoordinate):
    burnolAmbientEvenPart (tail c 4 (by norm_num))=
      (-1/2:ℂ) • Native.nativeUnitMuSource (barC c) 0:=by
  let t:=tail c 4 (by norm_num)
  have raw:(t:ℝ→ℂ)=ᵐ[volume]burnolRadiusMellinTailKernelRaw 4 c.value:=
    MemLp.coeFn_toLp (burnolRadiusMellinTailKernelRaw_memLp (by norm_num) c.value c.rightHalf)
  have reflected:=(negMeasurePreserving.quasiMeasurePreserving.ae raw)
  have reflectRead:=Lp.coeFn_compMeasurePreserving t negMeasurePreserving
  change (reflectL2 t:ℝ→ℂ)=ᵐ[volume] (t:ℝ→ℂ) ∘ (fun x=>-x) at reflectRead
  unfold burnolAmbientEvenPart
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (1/2:ℂ) (t+reflectL2 t),Lp.coeFn_add t (reflectL2 t),
    Lp.coeFn_smul (-1/2:ℂ) (Native.nativeUnitMuSource (barC c) 0),
    raw,reflected,reflectRead,Native.native_unit_source_zero (barC c)]
    with x scalar sumRead nativeScalar direct reverse reflection native
  change ((1/2:ℂ) • (t+reflectL2 t):BurnolL2) x=_
  rw [scalar,Pi.smul_apply,smul_eq_mul,sumRead,Pi.add_apply,nativeScalar,Pi.smul_apply,smul_eq_mul,
    reflection,Function.comp_apply,direct,reverse,native]
  change (1/2:ℂ)*(burnolRadiusMellinTailKernelRaw 4 c.value x+
    burnolRadiusMellinTailKernelRaw 4 c.value (-x))=
    (-1/2:ℂ)*burnolRadiusUnitTailRaw (star c.value) 4 x
  by_cases positive:0≤x
  · have negativeTail:¬4 < -x:=by linarith
    simp only [burnolRadiusMellinTailKernelRaw,mem_Ioi,burnolRadiusUnitTailRaw,
      abs_of_nonneg positive,if_neg negativeTail]
    by_cases outside:4<x <;> simp [outside]
    ring
  · have negative:x<0:=lt_of_not_ge positive
    have positiveTail:¬4<x:=by linarith
    simp only [burnolRadiusMellinTailKernelRaw,mem_Ioi,burnolRadiusUnitTailRaw,
      abs_of_neg negative,if_neg positiveTail]
    by_cases outside:4 < -x <;> simp [outside]
    ring

private theorem even_dilation (shift:ℝ) (v:BurnolL2):
    burnolAmbientEvenPart (burnolMultiplicativeDilation shift v)=
      burnolMultiplicativeDilation shift (burnolAmbientEvenPart v):=by
  unfold burnolAmbientEvenPart
  rw [reflectL2_burnolMultiplicativeDilation,map_smul,map_add]

private theorem even_smul (scalar:ℂ) (v:BurnolL2):
    burnolAmbientEvenPart (scalar • v)=scalar • burnolAmbientEvenPart v:=by
  unfold burnolAmbientEvenPart
  rw [map_smul]
  module

def nativeTailShift:ℝ:=Real.log 16

def nativeTailFactor (c:BurnolCompletedMellinCoordinate):ℂ:=
  (-1/2:ℂ)/fullMellinTranslationCharacter (star c.value) nativeTailShift

def nativeFirstLogTail (c:BurnolCompletedMellinCoordinate):BurnolL2:=
  nativeTailFactor c • burnolMultiplicativeDilation nativeTailShift
    (Native.nativeUnitMuSource (barC c) 1)

def firstLogTailRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=
  if q < |x| then -((|x|:ℝ):ℂ)^(-star c.value)*(Real.log (|x|/q):ℂ) else 0

/-- The generated source has the entire original q-tail logarithm, on both half axes. -/
theorem actual_native_log_profile (c:BurnolCompletedMellinCoordinate):
    (nativeFirstLogTail c:ℝ→ℂ)=ᵐ[volume] firstLogTailRaw c:=by
  have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp nativeTailShift*x) volume volume:=by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
        (r:=Real.exp nativeTailShift) (Real.exp_ne_zero nativeTailShift))
  have stretch:Real.exp nativeTailShift=16:=by
    unfold nativeTailShift
    rw [Real.exp_log (by norm_num:(0:ℝ)<16)]
  filter_upwards [Lp.coeFn_smul (nativeTailFactor c)
      (burnolMultiplicativeDilation nativeTailShift (Native.nativeUnitMuSource (barC c) 1)),
    burnolMultiplicativeDilation_coeFn nativeTailShift (Native.nativeUnitMuSource (barC c) 1),
    scale.ae (Native.native_unit_source_profile (barC c) 1)]
    with x scalar dilation raw
  change (nativeTailFactor c • burnolMultiplicativeDilation nativeTailShift
    (Native.nativeUnitMuSource (barC c) 1):BurnolL2) x=_
  rw [scalar,Pi.smul_apply,smul_eq_mul,dilation]
  change nativeTailFactor c*((Real.exp (nativeTailShift/2):ℂ)*
    Native.nativeUnitMuSource (barC c) 1 (Real.exp nativeTailShift*x))=firstLogTailRaw c x
  rw [raw]
  have absolute:|Real.exp nativeTailShift*x|=Real.exp nativeTailShift*|x|:=by
    rw [abs_mul,abs_of_pos (Real.exp_pos nativeTailShift)]
  have landing:4 < |Real.exp nativeTailShift*x| ↔ q < |x|:=by
    rw [absolute,stretch]
    constructor <;> intro h <;> linarith
  unfold Native.nativeUnitMuRaw firstLogTailRaw
  by_cases outside:q < |x|
  · rw [if_pos outside,if_pos (landing.mpr outside),absolute]
    have halfDensity:=realExp_cpow_halfDensity (by linarith : 0 < |x|) c.value nativeTailShift
    have logArgument:Real.exp nativeTailShift*|x|/4=|x|/q:=by rw [stretch];ring
    simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,Nat.factorial_one,
      Nat.cast_one,div_one,pow_one,neg_neg]
    rw [logArgument]
    calc
      _=nativeTailFactor c*2*((Real.exp (nativeTailShift/2):ℂ)*
          ((Real.exp nativeTailShift*|x|:ℝ):ℂ)^(-star c.value))*(Real.log (|x|/q):ℂ):=by ring
      _=_:=by
        rw [halfDensity]
        have nonzero:fullMellinTranslationCharacter (star c.value) nativeTailShift≠0:=Complex.exp_ne_zero _
        have factor:nativeTailFactor c*2*fullMellinTranslationCharacter (star c.value) nativeTailShift= -1:=by
          calc
            _=((-1/2:ℂ)*2)*((fullMellinTranslationCharacter (star c.value) nativeTailShift)⁻¹*
                fullMellinTranslationCharacter (star c.value) nativeTailShift):=by unfold nativeTailFactor;ring
            _=_:=by rw [inv_mul_cancel₀ nonzero];norm_num
        calc
          _=(nativeTailFactor c*2*fullMellinTranslationCharacter (star c.value) nativeTailShift)*
              ((|x|:ℝ):ℂ)^(-star c.value)*(Real.log (|x|/q):ℂ):=by ring
          _=_:=by rw [factor];ring
  · rw [if_neg outside,if_neg (fun h=>outside (landing.mp h))]
    ring

private theorem native_zero_tail (c:BurnolCompletedMellinCoordinate):
    burnolAmbientEvenPart (tail c q (by norm_num))=
      nativeTailFactor c • burnolMultiplicativeDilation nativeTailShift
        (Native.nativeUnitMuSource (barC c) 0):=by
  have moved:=burnolRadiusMellinTail_dilation (by norm_num:(0:ℝ)<4) c nativeTailShift
  have scale:(4:ℝ)*Real.exp (-nativeTailShift)=q:=by
    unfold nativeTailShift
    rw [Real.exp_neg,Real.exp_log (by norm_num:(0:ℝ)<16)]
    norm_num
  simp only [scale] at moved
  change burnolMultiplicativeDilation nativeTailShift (tail c 4 (by norm_num))=
    fullMellinTranslationCharacter (star c.value) nativeTailShift • tail c q (by norm_num) at moved
  have projected:=congrArg burnolAmbientEvenPart moved
  rw [even_dilation,even_smul,native_even_tail,map_smul] at projected
  have nonzero:fullMellinTranslationCharacter (star c.value) nativeTailShift≠0:=Complex.exp_ne_zero _
  calc
    _=(fullMellinTranslationCharacter (star c.value) nativeTailShift)⁻¹ •
        ((-1/2:ℂ) • burnolMultiplicativeDilation nativeTailShift
          (Native.nativeUnitMuSource (barC c) 0)):=by
      rw [projected,inv_smul_smul₀ nonzero]
    _=_:=by unfold nativeTailFactor;module

/-- Original R on the actual reciprocal unit source supplies the resonant first log tail. -/
theorem actual_resonant_tail_source (c:BurnolCompletedMellinCoordinate):
    burnolDirectRightResolvent (star c.value/2)
      (burnolAmbientEvenPart (tail c q (by norm_num)))=nativeFirstLogTail c:=by
  have right:1/4<(star c.value/2).re:=by
    rw [Complex.div_re];simp only [Complex.star_def,Complex.conj_re];norm_num;linarith [c.rightHalf]
  rw [native_zero_tail,burnolDirectRightResolvent_smul,burnolDirectRightResolvent_dilation]
  change nativeTailFactor c • burnolMultiplicativeDilation nativeTailShift
    (burnolDirectRightResolvent ((barC c).value/2) (Native.nativeUnitMuSource (barC c) 0))=_
  rw [Native.native_unit_source_action]
  rfl

/-- This is the complete resonant tail of the actual upward source action; no tail is set to zero. -/
theorem actual_resonant_tail_price (c:BurnolCompletedMellinCoordinate) (v:BurnolL2)
    (even:reflectL2 v=v):
    burnolRadiusMellinTailEvaluator q (by norm_num) c.value c.rightHalf
      (sourceVolterraResolvent c v)=inner ℂ (nativeFirstLogTail c) v:=by
  have right:1/4<(star c.value/2).re:=by
    rw [Complex.div_re];simp only [Complex.star_def,Complex.conj_re];norm_num;linarith [c.rightHalf]
  have adjoint:=OriginalKCompactAdjointRSource.actual_original_R_adjoint
    (star c.value/2) right v (burnolAmbientEvenPart (tail c q (by norm_num)))
  have inputEven:reflectL2 (sourceVolterraResolvent c v)=sourceVolterraResolvent c v:=by
    rw [sourceVolterraResolvent_reflect,even]
  have sourceEq:FiniteMobiusResolventFlux.Rplus (star (star c.value/2)) v=
      sourceVolterraResolvent c v:=by
    rw [star_div₀,star_star,star_ofNat]
    exact FiniteMobiusResolventFlux.Rplus_tate _
      (by rw [Complex.div_re];norm_num;linarith [c.rightHalf]) v
  rw [actual_resonant_tail_source,sourceEq] at adjoint
  have reverse:inner ℂ (nativeFirstLogTail c) v=
      inner ℂ (burnolAmbientEvenPart (tail c q (by norm_num))) (sourceVolterraResolvent c v):=by
    calc
      _=star (inner ℂ v (nativeFirstLogTail c)):=(inner_conj_symm _ _).symm
      _=star (inner ℂ (sourceVolterraResolvent c v)
          (burnolAmbientEvenPart (tail c q (by norm_num)))):=congrArg star adjoint
      _=_:=inner_conj_symm _ _
  change inner ℂ (tail c q (by norm_num)) (sourceVolterraResolvent c v)=_
  rw [←evenPart_left _ _ inputEven]
  exact reverse.symm

private theorem gap_price (v:BurnolL2):
    burnolAmbientGapCoefficient q v=
      burnolQuarterMeanCoefficient (burnolQuarterRestriction v):=by
  change ((‖intervalConstant q‖:ℂ)^2)⁻¹*inner ℂ (intervalConstant q)
    (burnolQuarterRestriction v)=inner ℂ (intervalConstant q) (burnolQuarterRestriction v)/
      ((‖intervalConstant q‖^2:ℝ):ℂ)
  push_cast
  ring

private theorem physical_constant_gap (v:BurnolPaAmbientCarrier):
    burnolQuarterRestriction (v:BurnolL2)=
      burnolAmbientGapCoefficient q (v:BurnolL2) • intervalConstant q:=by
  have centered:burnolQuarterMeanZeroProjection (burnolQuarterRestriction (v:BurnolL2))=0:=
    (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr v.property.1.1
  rw [burnolMeanZeroProjection_eq_sub_constant] at centered
  rw [gap_price]
  exact sub_eq_zero.mp centered

/-- The actual full power column pays its own quarter mean, before mean-zero projection. -/
theorem actual_power_mean (c:BurnolCompletedMellinCoordinate):
    burnolQuarterMeanCoefficient (SingularCounting.powerL2 (barC c))=
      (q:ℂ)^(c.value-1)/c.value:=by
  let raw:=SingularCounting.powerRaw (barC c)
  have native:IntervalIntegrable raw volume (-q) q:=by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num:(-q)≤q)).mpr
    exact MemLp.integrable (by norm_num) (SingularCounting.power_memLp (barC c))
  have lowerNative:IntervalIntegrable raw volume (-q) 0:=by
    apply native.mono_set
    rw [uIcc_of_le (by norm_num:(-q)≤(0:ℝ)),uIcc_of_le (by norm_num:(-q)≤q)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have upperNative:IntervalIntegrable raw volume 0 q:=by
    apply native.mono_set
    rw [uIcc_of_le (by norm_num:(0:ℝ)≤q),uIcc_of_le (by norm_num:(-q)≤q)]
    exact Icc_subset_Icc (by norm_num) le_rfl
  have negative:(∫ x:ℝ in (-q)..0,raw x)=∫ x:ℝ in 0..q,raw x:=by
    have moved:=intervalIntegral.integral_comp_neg (f:=raw) (a:=0) (b:=q)
    simpa only [raw,SingularCounting.powerRaw,abs_neg,neg_zero] using moved.symm
  have positive:(∫ x:ℝ in 0..q,raw x)=(q:ℂ)^c.value/c.value:=by
    have profile:(∫ x:ℝ in 0..q,raw x)=∫ x:ℝ in 0..q,(x:ℂ)^(c.value-1):=by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with x inside
      rw [uIoc_of_le (by norm_num:(0:ℝ)≤q)] at inside
      simp only [raw,SingularCounting.powerRaw,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,
        abs_of_pos inside.1]
    have nonzero:c.value≠0:=by
      intro h
      have bound:=c.rightHalf
      rw [h] at bound
      norm_num at bound
    rw [profile,integral_cpow (Or.inl (by
      change -1<c.value.re-1
      linarith [c.rightHalf]))]
    simp only [sub_add_cancel,Complex.ofReal_zero,Complex.zero_cpow nonzero,sub_zero]
  rw [OriginalRieszSource.Constructor.mean_integral,
    integral_congr_ae (SingularCounting.power_coeFn (barC c))]
  change (2:ℂ)*(∫ x:ℝ in Icc (-q) q,raw x)=_
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num:(-q)≤q),
    ←intervalIntegral.integral_add_adjacent_intervals lowerNative upperNative,negative,positive]
  have power:(q:ℂ)^c.value=(q:ℂ)^(c.value-1)*(q:ℂ):=by
    calc
      _=(q:ℂ)^((c.value-1)+1):=by congr 1;ring
      _=_:=by rw [Complex.cpow_add _ _ (by norm_num:(q:ℂ)≠0),Complex.cpow_one]
  rw [power]
  norm_num
  ring

/-- The complete resonant ambient scalar retains the generated quarter mean and the native log tail. -/
theorem actual_resonant_ambient_price (c:BurnolCompletedMellinCoordinate) (v:BurnolPaAmbientCarrier):
    burnolAmbientCompletedMellinEvaluator c (sourceVolterraResolvent c (v:BurnolL2))=
      burnolRadiusMellinGapMoment q c.value*
        (2*burnolAmbientGapCoefficient q (v:BurnolL2)/(1-c.value)-
          2*burnolAmbientCompletedMellinEvaluator c (v:BurnolL2)*
            burnolQuarterMeanCoefficient (SingularCounting.powerL2 (barC c)))+
        inner ℂ (nativeFirstLogTail c) (v:BurnolL2):=by
  have even:reflectL2 (v:BurnolL2)=(v:BurnolL2):=mem_evenL2ClosedFace_iff.mp v.property.2
  have quarter:=conjugate_volterra_quarter (barC c) (v:BurnolL2)
    (burnolAmbientGapCoefficient q (v:BurnolL2)) (physical_constant_gap v) even
  have double:barC (barC c)=c:=by
    cases c
    simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  rw [double] at quarter
  simp only [show star (barC c).value=c.value from star_star c.value] at quarter
  change burnolQuarterRestriction (sourceVolterraResolvent c (v:BurnolL2))=
    (2*burnolAmbientGapCoefficient q (v:BurnolL2)/(1-c.value)) • intervalConstant q+
    (-2*(burnolRadiusMellinTailEvaluator q (by norm_num) c.value c.rightHalf (v:BurnolL2)+
      burnolAmbientGapCoefficient q (v:BurnolL2)*(q:ℂ)^(1-c.value)/(1-c.value))) •
      SingularCounting.powerL2 (barC c) at quarter
  have scalar:burnolRadiusMellinTailEvaluator q (by norm_num) c.value c.rightHalf (v:BurnolL2)+
      burnolAmbientGapCoefficient q (v:BurnolL2)*(q:ℂ)^(1-c.value)/(1-c.value)=
      burnolAmbientCompletedMellinEvaluator c (v:BurnolL2):=by
    change _=burnolRadiusMellinGapMoment q c.value*burnolAmbientGapCoefficient q (v:BurnolL2)+
      burnolRadiusMellinTailEvaluator q (by norm_num) c.value c.rightHalf (v:BurnolL2)
    unfold burnolRadiusMellinGapMoment
    ring
  rw [scalar] at quarter
  change burnolRadiusMellinGapMoment q c.value*
    burnolAmbientGapCoefficient q (sourceVolterraResolvent c (v:BurnolL2))+
    burnolRadiusMellinTailEvaluator q (by norm_num) c.value c.rightHalf
      (sourceVolterraResolvent c (v:BurnolL2))=_
  rw [actual_resonant_tail_price c _ even,gap_price,quarter]
  have normal:burnolQuarterMeanCoefficient (intervalConstant q)=1:=mean_constant
  unfold burnolQuarterMeanCoefficient at normal
  unfold burnolQuarterMeanCoefficient
  rw [inner_add_right,inner_smul_right,inner_smul_right]
  linear_combination burnolRadiusMellinGapMoment q c.value*
    (2*burnolAmbientGapCoefficient q (v:BurnolL2)/(1-c.value))*normal

/-- The paid full mean gives its exact rational contact at the original parameter. -/
theorem actual_resonant_denominator_price (c:BurnolCompletedMellinCoordinate) (v:BurnolPaAmbientCarrier):
    burnolAmbientCompletedMellinEvaluator c (sourceVolterraResolvent c (v:BurnolL2))=
      2*burnolRadiusMellinGapMoment q c.value*burnolAmbientGapCoefficient q (v:BurnolL2)/(1-c.value)-
        2*burnolAmbientCompletedMellinEvaluator c (v:BurnolL2)/(c.value*(1-c.value))+
        inner ℂ (nativeFirstLogTail c) (v:BurnolL2):=by
  rw [actual_resonant_ambient_price,actual_power_mean]
  have nonzero:c.value≠0:=by
    intro h
    have bound:=c.rightHalf
    rw [h] at bound
    norm_num at bound
  have oneSub:1-c.value≠0:=by
    intro h
    have real:=congrArg Complex.re h
    simp only [Complex.sub_re,Complex.one_re,Complex.zero_re] at real
    linarith [c.belowOne]
  have inverse:(q:ℂ)^(1-c.value)*(q:ℂ)^(c.value-1)=1:=by
    rw [←Complex.cpow_add _ _ (by norm_num:(q:ℂ)≠0),
      show (1-c.value)+(c.value-1)=0 by ring,Complex.cpow_zero]
  have rational:burnolRadiusMellinGapMoment q c.value*
      (2*burnolAmbientCompletedMellinEvaluator c (v:BurnolL2)*((q:ℂ)^(c.value-1)/c.value))=
      2*burnolAmbientCompletedMellinEvaluator c (v:BurnolL2)/(c.value*(1-c.value)):=by
    unfold burnolRadiusMellinGapMoment
    field_simp [nonzero,oneSub]
    linear_combination burnolAmbientCompletedMellinEvaluator c (v:BurnolL2)*inverse
  rw [mul_sub,rational]
  ring

end OriginalKFiniteOrderRelease.UnitMellin.ResonantLogTailSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
