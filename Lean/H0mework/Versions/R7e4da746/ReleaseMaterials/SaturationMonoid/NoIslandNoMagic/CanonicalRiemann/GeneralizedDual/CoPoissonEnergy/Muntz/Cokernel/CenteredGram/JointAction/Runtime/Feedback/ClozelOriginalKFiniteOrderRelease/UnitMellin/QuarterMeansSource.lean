import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitFourier.FourierPhysical
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResonantLogTailSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.UnitMellin.QuarterMeansSource
open Complex MeasureTheory Set Filter BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
open private dirichlet_inner from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitFourier.Gap
open private power_succ_left from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
open private conjugate_volterra_quarter from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.HQuarterSource

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c"=>burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m"=>generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "U"=>OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half
include nontrivial

private theorem original_unit_fourier_gap:
    burnolQuarterRestriction (fourierL2 (burnolUnitTailResponse c 4))=
      (-(4:ℂ)^(1-(c).value)/(1-(c).value)) • intervalConstant q:=by
  let character:=fullMellinTranslationCharacter (c).value (-Real.log 4)
  have radius:(1:ℝ)*Real.exp (Real.log 4)=4:=by
    rw [one_mul,Real.exp_log (by norm_num:(0:ℝ)<4)]
  have action:=congrArg fourierL2 (burnolUnitTailResponse_radius_dilation c 1
    (by norm_num) (by norm_num) (-Real.log 4) (by rw [neg_neg,radius];norm_num))
  rw [fourierL2_burnolMultiplicativeDilation,neg_neg,map_smul,radius] at action
  have factor:character*(4:ℂ)^(1-(c).value)=(Real.exp (Real.log 4/2):ℂ):=by
    unfold character fullMellinTranslationCharacter
    rw [Complex.cpow_def_of_ne_zero (by norm_num:(4:ℂ)≠0),
      show Complex.log (4:ℂ)=(Real.log 4:ℂ) from (Complex.ofReal_log (by norm_num:(0:ℝ)≤4)).symm,
      ←Complex.exp_add,Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>(4:ℝ)*x) volume volume:=by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (r:=(4:ℝ)) (by norm_num))
  have raw:=scale.ae (burnolZeroOwnedUnitFourier_dirichlet_coeFn observation nontrivial half.down)
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (fourierL2 (burnolUnitTailResponse c 4)),
    Lp.coeFn_smul (-(4:ℂ)^(1-(c).value)/(1-(c).value)) (intervalConstant q),intervalConstant_coeFn q,
    ae_restrict_of_ae (Lp.coeFn_smul character (fourierL2 (burnolUnitTailResponse c 4))),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn (Real.log 4) (fourierL2 (burnolUnitTailResponse c 1))),
    ae_restrict_of_ae raw,ae_restrict_mem (measurableSet_symmetricInterval q)]
    with x restricted scalar constant acted dilation profile inside
  have read:=congrArg (fun v:BurnolL2=>v x) action
  rw [acted,dilation] at read
  change (Real.exp (Real.log 4/2):ℂ)*fourierL2 (burnolUnitTailResponse c 1)
    (Real.exp (Real.log 4)*x)=character*fourierL2 (burnolUnitTailResponse c 4) x at read
  rw [Real.exp_log (by norm_num:(0:ℝ)<4),profile] at read
  have small:|4*x|≤(1:ℝ):=by
    rw [abs_mul,abs_of_pos (by norm_num:(0:ℝ)<4)]
    linarith [abs_le.mpr inside]
  rw [dirichlet_inner _ _ small,←factor] at read
  change character*(4:ℂ)^(1-(c).value)* -(1/(1-(c).value))=
    character*fourierL2 (burnolUnitTailResponse c 4) x at read
  have nonzero:character≠0:=Complex.exp_ne_zero _
  have value:fourierL2 (burnolUnitTailResponse c 4) x= -(4:ℂ)^(1-(c).value)/(1-(c).value):=by
    apply mul_left_cancel₀ nonzero
    linear_combination -read
  change burnolQuarterRestriction (fourierL2 (burnolUnitTailResponse c 4)) x=_
  change burnolQuarterRestriction (fourierL2 (burnolUnitTailResponse c 4)) x=
    fourierL2 (burnolUnitTailResponse c 4) x at restricted
  rw [restricted,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one]
  exact value

/-- The exact lower Fourier gaps are generated geometrically by the same R action and its paid lower reads. -/
theorem actual_fourier_quarter_power (j:Nat) (before:j<m):
    burnolQuarterRestriction (fourierL2 (U j))=
      ((2/(1-(c).value))^j*(-(4:ℂ)^(1-(c).value)/(1-(c).value))) • intervalConstant q:=by
  induction j with
  | zero => simpa only [OriginalKFiniteOrderRelease.UnitPowerSource.unitPower,
      CombSource.Division.rawIterate,pow_zero,one_mul,one_apply_eq_self] using
      original_unit_fourier_gap observation nontrivial half
  | succ j previous =>
    have lower:j<m:=by omega
    have ih:=previous lower
    let p:BurnolPaAmbientCarrier:=⟨U j,OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_physical
      observation nontrivial half j lower⟩
    let fp:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius p
    let gamma:ℂ:=(2/(1-(c).value))^j*(-(4:ℂ)^(1-(c).value)/(1-(c).value))
    have gap:burnolQuarterRestriction (fp:BurnolL2)=gamma • intervalConstant q:=ih
    have mean:burnolAmbientGapCoefficient q (fp:BurnolL2)=gamma:=by
      change burnolConstantGapCoefficient q fp=gamma
      exact burnolConstantGapCoefficient_eq q (by norm_num) fp gamma gap.symm
    have even:reflectL2 (fp:BurnolL2)=(fp:BurnolL2):=mem_evenL2ClosedFace_iff.mp fp.property.2
    have zero:burnolAmbientCompletedMellinEvaluator c (fp:BurnolL2)=0:=by
      have restrict:=congrArg (fun r:BurnolPaAmbientCarrier→L[ℂ]ℂ=>r fp)
        (burnolAmbientCompletedMellinEvaluator_restrict c)
      change burnolAmbientCompletedMellinEvaluator c (fp:BurnolL2)=burnolCompletedMellinEvaluator c fp at restrict
      rw [restrict,←burnolCompletedMellinRieszVector_readback]
      have moved:=(evenFaceFourierEquiv burnolUnscaledCommonGapRadius).inner_map_map
        (burnolCompletedMellinRieszVector c) fp
      have invol:(evenFaceFourierEquiv burnolUnscaledCommonGapRadius) fp=p:=
        evenFaceFourier_involutive burnolUnscaledCommonGapRadius p
      rw [invol] at moved
      rw [←moved]
      exact OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_fourier_low observation nontrivial half j before
    have quarter:=conjugate_volterra_quarter (barC c) (fp:BurnolL2) gamma gap even
    have double:barC (barC c)=c:=by cases c;simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
    rw [double] at quarter
    simp only [show star (barC c).value=(c).value from star_star (c).value] at quarter
    have scalar:burnolRadiusMellinTailEvaluator q (by norm_num) (c).value (c).rightHalf (fp:BurnolL2)+
        gamma*(q:ℂ)^(1-(c).value)/(1-(c).value)=0:=by
      have actual:burnolAmbientCompletedMellinEvaluator c (fp:BurnolL2)=
          gamma*(q:ℂ)^(1-(c).value)/(1-(c).value)+
            burnolRadiusMellinTailEvaluator q (by norm_num) (c).value (c).rightHalf (fp:BurnolL2):=by
        change burnolRadiusMellinGapMoment q (c).value*burnolAmbientGapCoefficient q (fp:BurnolL2)+
          burnolRadiusMellinTailEvaluator q (by norm_num) (c).value (c).rightHalf (fp:BurnolL2)=_
        rw [mean]
        unfold burnolRadiusMellinGapMoment
        ring
      rw [actual] at zero
      linear_combination zero
    rw [scalar,mul_zero,zero_smul,add_zero] at quarter
    have step:=power_succ_left observation half j (burnolUnitTailResponse c 4)
    have right:1/4<((c).value/2).re:=by rw [Complex.div_re];norm_num;linarith [(c).rightHalf]
    change U (j+1)=burnolDirectRightResolvent ((c).value/2) (U j) at step
    rw [step,FiniteMobiusResolventFlux.fourier_R _ right,FiniteMobiusResolventFlux.Rplus_tate _ right]
    change burnolQuarterRestriction (sourceVolterraResolvent c (fp:BurnolL2))=_
    rw [quarter,pow_succ]
    unfold gamma
    module

/-- The first nonconstant Fourier gap is generated at the original exact Xi order, with its full constant mean. -/
theorem actual_top_fourier_quarter_power:
    burnolQuarterRestriction (fourierL2 (U m))=
      (2*((2/(1-(c).value))^(m-1)*(-(4:ℂ)^(1-(c).value)/(1-(c).value)))/(1-(c).value)) •
        intervalConstant q+
      (-2*burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation) •
        SingularCounting.powerL2 (barC c):=by
  have positive:0<m:=generatedRiemannXiZeroOrder_pos observation nontrivial
  let p:BurnolPaAmbientCarrier:=⟨U (m-1),OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_physical
    observation nontrivial half (m-1) (by omega)⟩
  let fp:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius p
  let gamma:ℂ:=(2/(1-(c).value))^(m-1)*(-(4:ℂ)^(1-(c).value)/(1-(c).value))
  have gap:burnolQuarterRestriction (fp:BurnolL2)=gamma • intervalConstant q:=
    actual_fourier_quarter_power observation nontrivial half (m-1) (by omega)
  have mean:burnolAmbientGapCoefficient q (fp:BurnolL2)=gamma:=by
    change burnolConstantGapCoefficient q fp=gamma
    exact burnolConstantGapCoefficient_eq q (by norm_num) fp gamma gap.symm
  have even:reflectL2 (fp:BurnolL2)=(fp:BurnolL2):=mem_evenL2ClosedFace_iff.mp fp.property.2
  have top:burnolAmbientCompletedMellinEvaluator c (fp:BurnolL2)=
      burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation:=by
    have restrict:=congrArg (fun r:BurnolPaAmbientCarrier→L[ℂ]ℂ=>r fp)
      (burnolAmbientCompletedMellinEvaluator_restrict c)
    change burnolAmbientCompletedMellinEvaluator c (fp:BurnolL2)=burnolCompletedMellinEvaluator c fp at restrict
    rw [restrict,←burnolCompletedMellinRieszVector_readback]
    have moved:=(evenFaceFourierEquiv burnolUnscaledCommonGapRadius).inner_map_map
      (burnolCompletedMellinRieszVector c) fp
    have invol:(evenFaceFourierEquiv burnolUnscaledCommonGapRadius) fp=p:=
      evenFaceFourier_involutive burnolUnscaledCommonGapRadius p
    rw [invol] at moved
    rw [←moved]
    exact OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_fourier_top observation nontrivial half
  have quarter:=conjugate_volterra_quarter (barC c) (fp:BurnolL2) gamma gap even
  have double:barC (barC c)=c:=by cases c;simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  rw [double] at quarter
  simp only [show star (barC c).value=(c).value from star_star (c).value] at quarter
  have scalar:burnolRadiusMellinTailEvaluator q (by norm_num) (c).value (c).rightHalf (fp:BurnolL2)+
      gamma*(q:ℂ)^(1-(c).value)/(1-(c).value)=
        burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation:=by
    have actual:burnolAmbientCompletedMellinEvaluator c (fp:BurnolL2)=
        gamma*(q:ℂ)^(1-(c).value)/(1-(c).value)+
          burnolRadiusMellinTailEvaluator q (by norm_num) (c).value (c).rightHalf (fp:BurnolL2):=by
      change burnolRadiusMellinGapMoment q (c).value*burnolAmbientGapCoefficient q (fp:BurnolL2)+
        burnolRadiusMellinTailEvaluator q (by norm_num) (c).value (c).rightHalf (fp:BurnolL2)=_
      rw [mean]
      unfold burnolRadiusMellinGapMoment
      ring
    rw [actual] at top
    linear_combination top
  rw [scalar] at quarter
  have step:=power_succ_left observation half (m-1) (burnolUnitTailResponse c 4)
  have right:1/4<((c).value/2).re:=by rw [Complex.div_re];norm_num;linarith [(c).rightHalf]
  change U (m-1+1)=burnolDirectRightResolvent ((c).value/2) (U (m-1)) at step
  rw [show m-1+1=m by omega] at step
  rw [step,FiniteMobiusResolventFlux.fourier_R _ right,FiniteMobiusResolventFlux.Rplus_tate _ right]
  exact quarter

end OriginalKFiniteOrderRelease.UnitMellin.QuarterMeansSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
