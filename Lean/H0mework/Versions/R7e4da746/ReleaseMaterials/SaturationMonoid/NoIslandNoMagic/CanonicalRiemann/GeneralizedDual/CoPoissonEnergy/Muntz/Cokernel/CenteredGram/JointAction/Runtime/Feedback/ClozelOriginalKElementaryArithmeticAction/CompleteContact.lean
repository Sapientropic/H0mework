import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CoreLogCancellation
import H0mework.Versions.R7e4da746.Arithmetic.RieszForcing.ForcingCutoffPairing
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszSource BurnolPhysicalState.OriginalRieszSourceGreen
open BurnolPhysicalState.OriginalRieszFinitePairing BurnolPhysicalState.OriginalRieszFiniteColumns
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFixedBoundarySourceFibre OriginalKSourceResolventReconstruction
open OriginalKExteriorCoPoissonAction OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open OriginalRieszSource.Translator.ForcingMeanZero
open scoped InnerProductSpace Topology
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "C" => ConstantDual.seed
local notation "Y" => ConstantDual.value
local notation "TD" => TemperedDistribution ℝ ℂ
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
local notation "Hq" => BurnolQuarterIntervalL2

/-- The whole unit-resolvent source supplies its Euler field before the mass is read. -/
theorem reverse_unit_euler (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    GapEuler.euler (elementaryReverseSource c zero:TD)+sourceRate c • (elementaryReverseSource c zero:TD)=
      (star c.value*GapEuler.gapMean q c) • (GapEuler.euler (Y:TD)+(1/2:ℂ) • (Y:TD)) := by
  have inverse:=sourceResolvent_euler c Y
  rw [elementary_reverse_unit_resolvent,unitResolventSource]
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 _)+sourceRate c •
    Lp.toTemperedDistributionCLM ℂ volume 2 _=_
  simp only [map_smul,map_sub,Lp.toTemperedDistributionCLM_apply]
  unfold sourceRate at inverse ⊢
  linear_combination (norm:=module)
    (-(star c.value*GapEuler.gapMean q c*((1-star c.value)/2))) • inverse

private theorem plateau_unit_flux :
    (GapEuler.euler (Y:TD)+(1/2:ℂ) • (Y:TD)) oneTest=-(2*q:ℝ) := by
  classical
  have derivative : GapEuler.euler (Y:TD)+(1/2:ℂ) • (Y:TD)=
      TemperedDistribution.derivCLM ℂ (GapEuler.position (Y:TD)) := by
    rw [GapEuler.derivative_position]
    unfold GapEuler.euler
    simp only [add_apply,ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply]
    module
  have actual : (fun x:ℝ=>(x:ℂ)*Y x*deriv oneTest x)=ᵐ[volume]
      (fun x:ℝ=>if x≤0 then (q:ℂ)*deriv oneTest x else -(q:ℂ)*deriv oneTest x) := by
    filter_upwards [ConstantDual.value_coeFn] with x raw
    by_cases inside:|x|≤q
    · rw [oneTest_deriv (abs_le.mp inside)]
      simp
    · have out : q < |x| := lt_of_not_ge inside
      rw [raw,ConstantDual.sawtooth_tail x out]
      by_cases sign:x≤0
      · rw [if_pos sign,abs_of_nonpos sign]
        have xn:(x:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (abs_pos.mp ((by norm_num : (0:ℝ)<q).trans out))
        push_cast
        field_simp
      · rw [if_neg sign,abs_of_pos (lt_of_not_ge sign)]
        have xn:(x:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_not_ge sign))
        push_cast
        field_simp
  let f:ℝ→ℂ:=fun x=>if x≤0 then (q:ℂ)*deriv oneTest x else -(q:ℂ)*deriv oneTest x
  have di:Integrable (deriv oneTest) := by
    convert! (SchwartzMap.derivCLM ℂ ℂ oneTest).integrable (μ:=volume) using 1
  have fi:Integrable f := Integrable.piecewise (s:=Iic (0:ℝ)) measurableSet_Iic (di.const_mul (q:ℂ)).integrableOn
    (di.const_mul (-(q:ℂ))).integrableOn
  have first : (∫x in Iic (0:ℝ),f x)=(q:ℂ) := by
    calc
      _ = ∫x in Iic (0:ℝ),(q:ℂ)*deriv oneTest x :=
        setIntegral_congr_fun measurableSet_Iic (fun x hx=>if_pos hx)
      _ = _ := by
        rw [integral_const_mul,HasCompactSupport.integral_Iic_deriv_eq
          (oneTest.smooth 1) oneTest_compact,oneTest_eq (by norm_num : (0:ℝ)∈Icc (-q) q),mul_one]
  have second : (∫x in Ioi (0:ℝ),f x)=(q:ℂ) := by
    calc
      _ = ∫x in Ioi (0:ℝ),-(q:ℂ)*deriv oneTest x :=
        setIntegral_congr_fun measurableSet_Ioi (fun x hx=>if_neg (not_le.mpr hx))
      _ = _ := by
        rw [integral_const_mul,HasCompactSupport.integral_Ioi_deriv_eq
          (oneTest.smooth 1) oneTest_compact,oneTest_eq (by norm_num : (0:ℝ)∈Icc (-q) q)]
        ring
  have mass:=setIntegral_union (Iic_disjoint_Ioi (a:=(0:ℝ)) le_rfl) measurableSet_Ioi fi.integrableOn fi.integrableOn
  rw [Iic_union_Ioi,setIntegral_univ,first,second] at mass
  rw [derivative,TemperedDistribution.derivCLM_apply_apply,GapEuler.position,
    TemperedDistribution.smulLeftCLM_apply_apply,Lp.toTemperedDistribution_apply]
  have growth:(fun x:ℝ=>(x:ℂ)).HasTemperateGrowth:=by fun_prop
  simp only [SchwartzMap.smulLeftCLM_apply growth,SchwartzMap.derivCLM_apply,smul_eq_mul,neg_apply]
  have read:(fun x:ℝ=> (x:ℂ)*(-deriv oneTest x)*Y x)=ᵐ[volume] fun x=>-f x := by
    filter_upwards [actual] with x source
    dsimp [f]
    linear_combination -source
  rw [integral_congr_ae read,integral_neg,mass]
  push_cast
  ring

private theorem plateau_reverse_reads (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    (elementaryReverseSource c zero:TD) oneTest=(1/2:ℂ)*reverseMean c zero ∧
    GapEuler.euler (elementaryReverseSource c zero:TD) oneTest=-(1/4:ℂ)*reverseMean c zero := by
  let v:=R (elementaryReverseSource c zero)
  have source:E v=elementaryReverseSource c zero:=elementary_reverse_support c zero
  have mass : (∫x in Ioc (-q) q,v x)=(1/2:ℂ)*reverseMean c zero := by
    have read:=Constructor.mean_integral v
    change reverseMean c zero=2*(∫x in Icc (-q) q,v x) at read
    rw [integral_Icc_eq_integral_Ioc] at read
    change reverseMean c zero=2*(∫x in Ioc (-q) q,v x) at read
    linear_combination -read/2
  have base:=Translator.ForcingCutoff.zeroExtension_pairing v (v:ℝ→ℂ) Filter.EventuallyEq.rfl oneTest
  have euler:=Translator.ForcingCutoff.euler_zeroExtension_pairing v (v:ℝ→ℂ) Filter.EventuallyEq.rfl oneTest
  have valueRead:(∫x in Ioc (-q) q,v x*oneTest x)=(1/2:ℂ)*reverseMean c zero := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx=>by rw [oneTest_eq (Ioc_subset_Icc_self hx),mul_one])]
    exact mass
  have derivativeRead:(∫x in Ioc (-q) q,((x:ℂ)*v x)*deriv oneTest x)=0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx=>by rw [oneTest_deriv (Ioc_subset_Icc_self hx),mul_zero]),integral_zero]
  rw [source,valueRead] at base
  rw [source,valueRead,derivativeRead] at euler
  exact ⟨base,by linear_combination euler⟩

/-- Both whole fluxes are paid by their actual source and the original exterior unit tail. -/
theorem reverse_unit_flux (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    (star c.value-1)*((1/2:ℂ)*reverseMean c zero)=-(2*q:ℝ)*star c.value*GapEuler.gapMean q c := by
  have law:=congrArg (fun value:TD=>value oneTest) (reverse_unit_euler c zero)
  simp only [add_apply,smul_apply,smul_eq_mul] at law
  have flux:=plateau_unit_flux
  simp only [add_apply,smul_apply,smul_eq_mul] at flux
  rw [(plateau_reverse_reads c zero).1,(plateau_reverse_reads c zero).2,flux] at law
  unfold sourceRate at law
  linear_combination law

private theorem reverse_mean_value (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    reverseMean c zero=star c.value*GapEuler.gapMean q c/(1-star c.value) := by
  have ne:1-star c.value≠0 := by
    intro hx
    have re:=congrArg Complex.re (sub_eq_zero.mp hx)
    simp only [one_re,star_def,conj_re] at re
    linarith [c.belowOne]
  apply (eq_div_iff ne).mpr
  have actual:=reverse_unit_flux c zero
  norm_num at actual
  change (star c.value-1)*(1/2*reverseMean c zero)=-(1/2*star c.value*GapEuler.gapMean q c) at actual
  linear_combination -2*actual

private theorem K_constant_read (c:BurnolCompletedMellinCoordinate) :
    inner ℂ (sourceKernel c) C=(1/2:ℂ)*star (positionMean c) := by
  rw [sourceKernel_original]
  have read : (fun x:ℝ=>inner ℂ ((burnolCompletedMellinRieszVector c:BurnolL2) x) (C x))=ᵐ[volume]
      (symmetricInterval q).indicator (fun _:ℝ=>star (positionMean c)) := by
    filter_upwards [burnolRieszState_ae_raw c,ConstantDual.seed_coeFn] with x raw seed
    rw [seed,ConstantDual.seedRaw]
    by_cases inside:x∈symmetricInterval q
    · rw [if_pos (abs_le.mpr inside),indicator_of_mem inside,raw,position_raw,if_pos inside,add_zero]
      simp [RCLike.inner_apply]
    · rw [if_neg (fun hx=>inside (abs_le.mp hx)),indicator_of_notMem inside]
      simp
  rw [L2.inner_def,integral_congr_ae read,integral_indicator (measurableSet_symmetricInterval q),integral_const]
  norm_num [symmetricInterval,real_smul]


private theorem dual_dilation (N:ℕ) (t:ℝ) (v:BurnolL2) :
    DualSource.source N (burnolMultiplicativeDilation t v)=
      burnolMultiplicativeDilation t (DualSource.source N v) := by
  have channel (a:ℝ) : ContinuousChannels.channel 1 a (burnolMultiplicativeDilation t v)=
      burnolMultiplicativeDilation t (ContinuousChannels.channel 1 a v) := by
    simp only [ContinuousChannels.channel,map_smul,burnolMultiplicativeDilation_add]
    rw [add_comm]
  unfold DualSource.source
  simp_rw [channel]
  rw [map_sub,map_sum]
  congr 1
  exact (burnolMultiplicativeDilation t).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable 1 N v)

private theorem gap_column_whole (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    E (gapFirstBandColumn c h:Hq)=burnolMultiplicativeDilation (Real.log 2)
      (gapDilationDifference c h+gapDilationDifference c (-h)) := by
  have whole:=compressed_core_whole c h nn bound
  rw [source_log_columns c h nn bound] at whole
  change E (-(1/2:ℂ) • ((gapFirstBandColumn c h:Hq)+(lossFirstBandColumn c h:Hq)))=_ at whole
  rw [map_smul,map_add,loss_firstBand_whole c h nn bound] at whole
  unfold positionCoreSource at whole
  rw [map_smul,map_add,map_add] at whole
  rw [map_add]
  linear_combination (norm:=module) (-2:ℂ) • whole

private theorem finite_log_read (state:BurnolQuarterMeanZeroCarrier) (N:ℕ) (pos:0<N) :
    inner ℂ C (DualSource.source N (E (state:Hq)))=inner ℂ SmallScaleLog.logL2 (state:Hq) := by
  rw [←CountingDual.source_pairing]
  have restriction : R (FiniteForcing.source N C)=WindowCounting.harmonicCoefficient N • intervalConstant q+SmallScaleLog.logL2 :=
    WindowCounting.constant_source N pos
  have adjoint:=ContinuousLinearMap.adjoint_inner_right R (FiniteForcing.source N C) (state:Hq)
  change inner ℂ (FiniteForcing.source N C) (E (state:Hq))=_ at adjoint
  rw [adjoint,restriction,inner_add_left,inner_smul_left]
  have mean:inner ℂ (intervalConstant q) (state:Hq)=0 :=
    (Submodule.mem_orthogonal _ _).mp state.property _ (Submodule.mem_span_singleton_self _)
  rw [mean,mul_zero,zero_add]

private theorem reverse_inward_constant_read (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (t:ℝ) (nn:0≤t) :
    inner ℂ C (burnolMultiplicativeDilation t (elementaryReverseSource c zero))=
      (Real.exp (-t/2):ℂ)*(1/2:ℂ)*reverseMean c zero := by
  have source:E (R (elementaryReverseSource c zero))=elementaryReverseSource c zero:=elementary_reverse_support c zero
  have restricted : R (burnolMultiplicativeDilation (-t) C)=
      (Real.exp (-t/2):ℂ) • intervalConstant q := by
    have scale : Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp (-t)*x) volume volume := by
      simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
        (r:=Real.exp (-t)) (Real.exp_ne_zero (-t)))
    apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (burnolMultiplicativeDilation (-t) C),
      ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn (-t) C),
      ae_restrict_of_ae (scale.ae ConstantDual.seed_coeFn),
      ae_restrict_mem (measurableSet_symmetricInterval q),
      Lp.coeFn_smul (Real.exp (-t/2):ℂ) (intervalConstant q),intervalConstant_coeFn q]
      with x restriction dilation seed inside scalar constant
    have stays : |Real.exp (-t)*x|≤q := by
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr nn)) (abs_nonneg x)).trans
        (by simpa only [one_mul] using abs_le.mpr inside)
    change R (burnolMultiplicativeDilation (-t) C) x=_ at restriction
    rw [restriction,dilation,burnolL2RawNormalizedDilation,seed,ConstantDual.seedRaw,if_pos stays,scalar]
    change (Real.exp (-t/2):ℂ)*1=(Real.exp (-t/2):ℂ)*intervalConstant q x
    rw [constant]
  have flipped:=(burnolMultiplicativeDilation (-t)).inner_map_eq_flip C (elementaryReverseSource c zero)
  rw [←burnolMultiplicativeDilation_neg_eq_symm,neg_neg] at flipped
  rw [←flipped,←source]
  have adjoint:=ContinuousLinearMap.adjoint_inner_right R (burnolMultiplicativeDilation (-t) C)
    (R (elementaryReverseSource c zero))
  change inner ℂ (burnolMultiplicativeDilation (-t) C) (E (R (elementaryReverseSource c zero)))=_ at adjoint
  rw [adjoint,restricted,inner_smul_left]
  have mean:inner ℂ (intervalConstant q) (R (elementaryReverseSource c zero))=(1/2:ℂ)*reverseMean c zero := by
    unfold reverseMean burnolQuarterMeanCoefficient
    rw [Complex.ofReal_pow,burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)]
    norm_num
    ring
  rw [mean]
  simp only [conj_ofReal]
  ring

/-- The actual finite dual programme reads the log contact of the complete two-scale gap word. -/
theorem gap_log_source_action (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    gapLogContact c h=
      ((Real.exp (h/2):ℂ)+(Real.exp (-h/2):ℂ)-2*pairedMellinTranslationCharacter (star c.value) h)*
        reverseMean c zero*inner ℂ (sourceKernel c) C := by
  let z:=elementaryReverseSource c zero
  let w:=gapDilationDifference c h+gapDilationDifference c (-h)
  let zword:=burnolMultiplicativeDilation h z+burnolMultiplicativeDilation (-h) z-
    (fullMellinTranslationCharacter (star c.value) h+fullMellinTranslationCharacter (star c.value) (-h)) • z
  have finite (N:ℕ) : DualSource.source N w=
      burnolMultiplicativeDilation h (DualSource.source N (elementarySource c))+
      burnolMultiplicativeDilation (-h) (DualSource.source N (elementarySource c))-
      (fullMellinTranslationCharacter (star c.value) h+fullMellinTranslationCharacter (star c.value) (-h)) •
        DualSource.source N (elementarySource c) := by
    change DualSource.source N ((burnolMultiplicativeDilation h (elementarySource c)-
      fullMellinTranslationCharacter (star c.value) h • elementarySource c)+
      (burnolMultiplicativeDilation (-h) (elementarySource c)-
      fullMellinTranslationCharacter (star c.value) (-h) • elementarySource c))=_
    rw [CountingDual.dual_eq_adjoint,map_add,map_sub,map_sub,map_smul,map_smul]
    simp only [←CountingDual.dual_eq_adjoint]
    change DualSource.source N (burnolMultiplicativeDilation h (elementarySource c))-_+
      (DualSource.source N (burnolMultiplicativeDilation (-h) (elementarySource c))-_) =_
    rw [dual_dilation,dual_dilation]
    module
  have limit:Tendsto (fun N:ℕ=>DualSource.source N w) atTop (𝓝 zword) := by
    have left:=((burnolMultiplicativeDilation h).continuous.tendsto z).comp (elementary_reverse_tendsto c zero)
    have right:=((burnolMultiplicativeDilation (-h)).continuous.tendsto z).comp (elementary_reverse_tendsto c zero)
    have center:=(elementary_reverse_tendsto c zero).const_smul
      (fullMellinTranslationCharacter (star c.value) h+fullMellinTranslationCharacter (star c.value) (-h))
    exact ((left.add right).sub center).congr' (Eventually.of_forall (fun N=>(finite N).symm))
  have compressed:Tendsto (fun N:ℕ=>DualSource.source N (E (gapFirstBandColumn c h:Hq))) atTop
      (𝓝 (burnolMultiplicativeDilation (Real.log 2) zword)) := by
    have actual:=((burnolMultiplicativeDilation (Real.log 2)).continuous.tendsto zword).comp limit
    apply actual.congr'
    filter_upwards [] with N
    rw [gap_column_whole c h nn bound,dual_dilation]
    rfl
  have logLimit:Tendsto (fun N:ℕ=>inner ℂ C (DualSource.source N (E (gapFirstBandColumn c h:Hq)))) atTop
      (𝓝 (inner ℂ SmallScaleLog.logL2 (gapFirstBandColumn c h:Hq))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N large
    exact (finite_log_read (gapFirstBandColumn c h) N (by omega)).symm
  have law:=tendsto_nhds_unique
    ((tendsto_const_nhds (x:=C)).inner (𝕜:=ℂ) compressed) logLimit
  dsimp [zword] at law
  rw [map_sub,map_add,map_smul,burnolMultiplicativeDilation_add,burnolMultiplicativeDilation_add,
    inner_sub_right,inner_add_right,inner_smul_right,
    reverse_inward_constant_read c zero (Real.log 2+h) (by linarith [Real.log_nonneg (by norm_num : (1:ℝ)≤2)]),
    reverse_inward_constant_read c zero (Real.log 2+-h) (by linarith),
    reverse_inward_constant_read c zero (Real.log 2) (Real.log_nonneg (by norm_num : (1:ℝ)≤2))] at law
  have plus:Real.exp (-(Real.log 2+h)/2)=Real.exp (-Real.log 2/2)*Real.exp (-h/2) := by
    rw [←Real.exp_add];congr 1;ring
  have minus:Real.exp (-(Real.log 2+-h)/2)=Real.exp (-Real.log 2/2)*Real.exp (h/2) := by
    rw [←Real.exp_add];congr 1;ring
  have coefficient:(Real.sqrt 2:ℂ)*(Real.exp (-Real.log 2/2):ℂ)=1 := by
    rw [neg_div,Real.exp_neg,Real.exp_half,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [Complex.ofReal_inv]
    exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne')
  change (Real.exp (-(Real.log 2+h)/2):ℂ)*(1/2:ℂ)*reverseMean c zero+
      (Real.exp (-(Real.log 2+-h)/2):ℂ)*(1/2:ℂ)*reverseMean c zero-
      (fullMellinTranslationCharacter (star c.value) h+fullMellinTranslationCharacter (star c.value) (-h))*
        ((Real.exp (-Real.log 2/2):ℂ)*(1/2:ℂ)*reverseMean c zero)=_ at law
  have reverseChar:fullMellinTranslationCharacter (star c.value) (-h)=
      reciprocalMellinTranslationCharacter (star c.value) h := by
    unfold fullMellinTranslationCharacter reciprocalMellinTranslationCharacter
    congr 1
    push_cast
    ring
  unfold gapLogContact
  rw [←law,plus,minus,Complex.ofReal_mul,Complex.ofReal_mul,K_constant_read,reverseChar]
  unfold pairedMellinTranslationCharacter
  calc
    _ = ((Real.sqrt 2:ℂ)*(Real.exp (-Real.log 2/2):ℂ))*
      (((Real.exp (h/2):ℂ)+(Real.exp (-h/2):ℂ)-
        fullMellinTranslationCharacter (star c.value) h-reciprocalMellinTranslationCharacter (star c.value) h)*
        reverseMean c zero*((1/2:ℂ)*star (positionMean c))) := by ring
    _ = _ := by rw [coefficient];ring

/-- Both contacts come from the same unit/Euler source, so the full combination is zero. -/
theorem complete_contact_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    (1/2:ℂ)*gapLogContact c h+
      (pairedMellinTranslationCharacter (star c.value) h-((Real.exp (h/2):ℂ)+(Real.exp (-h/2):ℂ))/2)*
        reverseMean c zero*inner ℂ (sourceKernel c) C=0 := by
  have gapAction:=gap_log_source_action c zero h nn bound
  rw [gapAction,reverse_mean_value c zero]
  ring

/-- The complete contact source is consumed in the original residual price. -/
theorem original_fixedResidual_complete_contact (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) (fixed:h=Real.log stageZeroSonineQ) :
    -burnolPaFixedShiftResidual c zero=
      (2*q:ℝ)*GapEuler.gapMean q c*
        (Complex.exp (sourceRate c*(h:ℂ))-(Real.exp (-h/2):ℂ))*inner ℂ (sourceKernel c) C-
      (1/2:ℂ)*inner ℂ (sourceKernel c) (collarSource c h)+coreCharacterDefect c h*kernelSelfSource c-
      (1/2:ℂ)*(inner ℂ (sourceKernel c) (FullUnit.fullSource c h 1)-
        inner ℂ (sourceKernel c) (fourierL2 (FullUnit.fullSource c h 0))) := by
  have price:=original_fixedResidual_gap_log_source c zero h nn bound fixed
  have contact:=complete_contact_source c zero h nn bound
  unfold coreCharacterDefect at price ⊢
  linear_combination price+contact

end OriginalKElementaryArithmeticAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
