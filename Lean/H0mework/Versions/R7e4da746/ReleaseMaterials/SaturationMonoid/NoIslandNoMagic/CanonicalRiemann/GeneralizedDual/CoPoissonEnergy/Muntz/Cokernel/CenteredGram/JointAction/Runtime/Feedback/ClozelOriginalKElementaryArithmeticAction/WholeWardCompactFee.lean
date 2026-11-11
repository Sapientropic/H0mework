import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeWardSourceBalance
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.WholeWardCompactFee
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open OriginalKExteriorCoPoissonAction WholeBForcingSource WholeWardSourceBalance
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "Q" => Constructor.zeroMean
local notation "ell" => CenteredCountingDual.logarithm
local notation "k" => CenteredCountingDual.constantFourier
local notation "DN" => CenteredCountingDual.reverse
local notation "CN" => CenteredCountingDual.forward
local notation "U" => unitResolventSource

private theorem forward_fourier (N:ℕ) (value:BurnolL2) :
    FiniteForcing.source N (fourierL2 value)=fourierL2 (DualSource.source N value) :=by
  have channel (a:ℝ) :ContinuousChannels.channel (-1) a (fourierL2 value)=fourierL2 (ContinuousChannels.channel 1 a value) :=by
    simp only [ContinuousChannels.channel,one_mul,neg_one_mul,map_smul,fourierL2_burnolMultiplicativeDilation]
  have integer (n:ℕ) :Channels.sourceChannel n (fourierL2 value)=fourierL2 (ContinuousChannels.channel 1 n value) :=by
    simpa only [ContinuousChannels.channel,Channels.sourceChannel,neg_one_mul] using channel n
  unfold FiniteForcing.source ContinuousChannels.normalization DualSource.source
  simp_rw [integer,channel]
  rw [map_sub,map_sum]
  congr 1
  exact fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable 1 N value)

private theorem b_fourier_mean (c:BurnolCompletedMellinCoordinate) :
    sourceFourierMean (sourceB c)=2*inner ℂ k (sourceB c) :=by
  have pairing:=quarter_fourier_pairing_of_reflection (intervalConstant q) (sourceB c:Hq)
    (burnolRieszSingleFourierSource_reflection_fixed c)
  have constant:inner ℂ (intervalConstant q) (burnolTruncatedFourier (sourceB c:Hq))=
      sourceFourierMean (sourceB c)/2 :=by
    unfold sourceFourierMean burnolQuarterMeanCoefficient
    rw [Complex.ofReal_pow,burnolIntervalConstant_norm_sq (by norm_num :(0:ℝ)<q)]
    norm_num
    ring
  have projected:inner ℂ k (sourceB c)=inner ℂ (burnolTruncatedFourier (intervalConstant q)) (sourceB c:Hq) :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (sourceB c) _
  rw [projected,pairing,constant]
  ring

private theorem whole_reverse_b (c:BurnolCompletedMellinCoordinate) (N:ℕ) (positive:0<N) :
    DualSource.source N (E (sourceB c:Hq))=E (DN N (sourceB c):Hq)+
      (2*inner ℂ SmallScaleLog.logL2 (sourceB c:Hq)) • ConstantDual.seed :=by
  have supported:=CenteredCountingDualSupport.source_support (sourceB c)
    (burnolRieszSingleFourierSource_reflection_fixed c) N positive
  have split:=Constructor.zeroMean_read (R (DualSource.source N (E (sourceB c:Hq))))
  change (DN N (sourceB c):Hq)=_ at split
  rw [split,map_sub,map_smul]
  change _=E (R (DualSource.source N (E (sourceB c:Hq))))-
    BCountingCocycle.sourceReverseMean c N • ConstantDual.seed+
      (2*inner ℂ SmallScaleLog.logL2 (sourceB c:Hq)) • ConstantDual.seed
  rw [←supported,BCountingCocycle.source_reverse_mean c N positive]
  module

private theorem finite_position_source (c:BurnolCompletedMellinCoordinate) (N:ℕ) (positive:0<N) :
    Q (R (FiniteForcing.source N (sourceKernel c)))=
      Q (R (FiniteForcing.source N (elementarySource c)))-sourceFourierMean (sourceB c) • ell :=by
  have fourier:Q (R (fourierL2 (DualSource.source N (E (sourceB c:Hq)))))=
      S (DN N (sourceB c))+(2*inner ℂ SmallScaleLog.logL2 (sourceB c:Hq)) • k :=by
    rw [whole_reverse_b c N positive,map_add,map_smul,map_add,map_smul,map_add,map_smul]
    rfl
  have commutator:=CountingJointEnergy.commutator N positive (sourceB c)
    (burnolRieszSingleFourierSource_reflection_fixed c)
  change CN N (sourceSB c)-S (DN N (sourceB c))=CountingJointEnergy.contact (sourceB c) at commutator
  change Q (R (CountingDual.sourceCLM N (sourceKernel c)))=_
  rw [sourceKernel,map_sub,map_add]
  simp only [CountingDual.sourceCLM_apply,forward_fourier,map_sub,map_add]
  rw [fourier]
  change Q (R (FiniteForcing.source N (elementarySource c)))+CN N (sourceSB c)-
    (S (DN N (sourceB c))+(2*inner ℂ SmallScaleLog.logL2 (sourceB c:Hq)) • k)=_
  have logPair:inner ℂ ell (sourceB c)=inner ℂ SmallScaleLog.logL2 (sourceB c:Hq) :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (sourceB c) _
  unfold CountingJointEnergy.contact at commutator
  rw [logPair] at commutator
  rw [b_fourier_mean c]
  linear_combination (norm:=module) commutator

private theorem position_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    Q (R (KCountingGram.value c))=Q (R (U c ConstantForward.value))-sourceFourierMean (sourceB c) • ell :=by
  have left:=(Constructor.zeroMean.continuous.tendsto _).comp ((burnolQuarterRestriction.continuous.tendsto _).comp (KCountingGram.forward_tendsto c zero))
  have right:=((Constructor.zeroMean.continuous.tendsto _).comp ((burnolQuarterRestriction.continuous.tendsto _).comp (WholeGramSource.elementary_forward_tendsto c))).sub_const
    (sourceFourierMean (sourceB c) • ell)
  have same:Tendsto (fun N:ℕ=>Q (R (FiniteForcing.source N (elementarySource c)))-
      sourceFourierMean (sourceB c) • ell) atTop (𝓝 (Q (R (KCountingGram.value c)))) :=by
    apply left.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N after
    change Q (R (FiniteForcing.source N (burnolCompletedMellinRieszVector c:BurnolL2)))=
      Q (R (FiniteForcing.source N (elementarySource c)))-sourceFourierMean (sourceB c) • ell
    rw [←sourceKernel_original c]
    exact finite_position_source c N (Nat.lt_of_lt_of_le (by decide:0<1) after)
  exact tendsto_nhds_unique same right

private theorem projected_pair (value:BurnolL2) (test:M) :
    inner ℂ value (E (test:Hq))=inner ℂ (Q (R value)) test :=by
  have adjoint:=ContinuousLinearMap.adjoint_inner_right R value (test:Hq)
  change inner ℂ value (E (test:Hq))=inner ℂ (R value) (test:Hq) at adjoint
  rw [adjoint]
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right test _).symm

private theorem forward_unit_fourier_gap :R (fourierL2 ConstantForward.value)=-(q:ℂ) • intervalConstant q :=by
  rw [ConstantFourier.original_square,ConstantFourier.reciprocal_value]
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 q),
    ae_restrict_of_ae (burnolSourceScalePrimitive_coeFn burnolUnitCountingPrimitiveL2 burnolUnitCountingPrimitiveRaw
      burnolUnitCountingPrimitive_memLp.coeFn_toLp q (by norm_num)),
    ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_smul (-(q:ℂ)) (intervalConstant q),intervalConstant_coeFn q] with x restricted scaled inside smulAt constantAt
  change R (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 q) x=( -(q:ℂ) • intervalConstant q:Hq) x
  change R (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 q) x=
    burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 q x at restricted
  rw [restricted,scaled,smulAt]
  change (q:ℂ)*burnolUnitCountingPrimitiveRaw (q*x)=-(q:ℂ)*intervalConstant q x
  rw [constantAt,burnolUnitCountingPrimitive_small]
  · ring
  · rw [abs_mul,abs_of_pos (by norm_num :(0:ℝ)<q)]
    nlinarith [abs_le.mpr inside]

private theorem full_forward_fourier_pair (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    inner ℂ (E (sourceSB c:Hq)) (fourierL2 (FullUnit.fullForward c h 0))=0 :=by
  obtain ⟨physical,inPa,actual⟩:=Submodule.mem_map.mp (exterior_wave_inPa c h nn bound 0)
  have gap:R (fourierL2 (exteriorWave c h 0))∈(ℂ ∙ intervalConstant q) :=by
    rw [←actual]
    exact physical.property.1.2
  have exterior:inner ℂ (E (sourceSB c:Hq)) (fourierL2 (exteriorWave c h 0))=0 :=by
    have adjoint:=ContinuousLinearMap.adjoint_inner_left R (fourierL2 (exteriorWave c h 0)) (sourceSB c:Hq)
    change inner ℂ (E (sourceSB c:Hq)) (fourierL2 (exteriorWave c h 0))=_ at adjoint
    rw [adjoint]
    exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp (sourceSB c).property _ gap)
  have unit:inner ℂ (E (sourceSB c:Hq)) (fourierL2 ConstantForward.value)=0 :=by
    have adjoint:=ContinuousLinearMap.adjoint_inner_left R (fourierL2 ConstantForward.value) (sourceSB c:Hq)
    change inner ℂ (E (sourceSB c:Hq)) (fourierL2 ConstantForward.value)=_ at adjoint
    rw [adjoint,forward_unit_fourier_gap,inner_smul_right]
    have mean:inner ℂ (sourceSB c:Hq) (intervalConstant q)=0 :=
      inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp (sourceSB c).property _ (Submodule.mem_span_singleton_self _))
    rw [mean,mul_zero]
  rw [FullUnit.fullForward,map_add,map_smul,inner_add_right,inner_smul_right,exterior,unit,mul_zero,add_zero]

private theorem shifted_ambient_fourier_gap (c:BurnolCompletedMellinCoordinate) (h:ℝ) (bound:h≤Real.log 2) :
    R (burnolMultiplicativeDilation h (fourierL2 (AmbientCounting.value c)))=0 :=by
  have qmp:=Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (Real.exp_ne_zero h)
  have moved:=qmp.ae (AmbientFourierRaw.original_fourier_coeFn c)
  have exponential:Real.exp h≤2 :=by
    calc
      _≤Real.exp (Real.log 2):=Real.exp_le_exp.mpr bound
      _=2:=Real.exp_log (by norm_num)
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (burnolMultiplicativeDilation h (fourierL2 (AmbientCounting.value c))),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn h (fourierL2 (AmbientCounting.value c))),
    ae_restrict_of_ae moved,ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_zero ℂ 2 (volume.restrict (symmetricInterval q))] with x restricted dilation raw inside zeroAt
  change R (burnolMultiplicativeDilation h (fourierL2 (AmbientCounting.value c))) x=
    burnolMultiplicativeDilation h (fourierL2 (AmbientCounting.value c)) x at restricted
  change fourierL2 (AmbientCounting.value c) (Real.exp h*x)=AmbientFourierRaw.raw c (Real.exp h*x) at raw
  rw [restricted,dilation,zeroAt]
  change (Real.exp (h/2):ℂ)*fourierL2 (AmbientCounting.value c) (Real.exp h*x)=0
  rw [raw,AmbientFourierRaw.raw_gap]
  · ring
  · rw [abs_mul,abs_of_pos (Real.exp_pos h)]
    have small:|x|≤q:=abs_le.mpr inside
    nlinarith [Real.exp_pos h,abs_nonneg x]

/-- The actual forward field of the original Fourier compact word, with both full B losses present. -/
def compactFourierForward (c:BurnolCompletedMellinCoordinate) (h:ℝ) :BurnolL2 :=
  -pairedMellinTranslationCharacter c.value h • AmbientCounting.value c+(1/2:ℂ) •
    (burnolMultiplicativeDilation (-h) (AmbientCounting.value c)-FullUnit.fullForward c h 0+
      burnolMultiplicativeDilation h (AmbientCounting.value c))

private theorem compact_fourier_forward_tendsto (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (compactFourier c h:Hq))) atTop
      (𝓝 (compactFourierForward c h)) :=by
  have left:=(AmbientCounting.original_ambient_limit c).const_smul (-pairedMellinTranslationCharacter c.value h)
  have plus:=((burnolMultiplicativeDilation h).continuous.tendsto _).comp (AmbientCounting.original_ambient_limit c)
  have minus:=(((burnolMultiplicativeDilation (-h)).continuous.tendsto _).comp (AmbientCounting.original_ambient_limit c)).sub
    (FullUnit.full_forward_tendsto c h nn 0)
  have total:=left.add ((minus.add plus).const_smul (1/2:ℂ))
  change Tendsto _ _ (𝓝 (compactFourierForward c h)) at total
  apply total.congr'
  filter_upwards [] with N
  have outward:E (meanZeroDilation (-h) (sourceB c):Hq)=
      burnolMultiplicativeDilation (-h) (E (sourceB c:Hq))-FullUnit.fullSource c h 0 :=by
    rw [outward_full_source_inventory h (sourceB c)]
    change _=_-fullWindowLoss h (sourceB c)
    module
  have input:E (compactFourier c h:Hq)= -pairedMellinTranslationCharacter c.value h • E (sourceB c:Hq)+
      (1/2:ℂ) • (burnolMultiplicativeDilation (-h) (E (sourceB c:Hq))-FullUnit.fullSource c h 0+
        burnolMultiplicativeDilation h (E (sourceB c:Hq))) :=by
    have second:=sourceSecondSB_actual c h nn
    change sourceSecondSB c h+meanZeroDilation (-h) (sourceEta c)=meanZeroDilation (-h) (sourceB c) at second
    unfold compactFourier
    rw [second,sourceFirstB_actual c h nn]
    change E (-pairedMellinTranslationCharacter c.value h • (sourceB c:Hq)+(1/2:ℂ) •
      ((meanZeroDilation (-h) (sourceB c):Hq)+(meanZeroDilation h (sourceB c):Hq)))=_
    rw [map_add,map_smul,map_smul,map_add,outward,inward_extension h nn]
  change _=CountingDual.sourceCLM N (E (compactFourier c h:Hq))
  rw [input,map_add,map_smul,map_smul,map_add,map_sub]
  simp only [CountingDual.sourceCLM_apply,SeedCounting.source_dilation,Function.comp_apply]
  rfl

private theorem return_fourier_compact_zero (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    inner ℂ (ReturnCounting.forwardValue c) (fourierL2 (E (compactFourier c h:Hq)))=0 :=by
  have left:=(ReturnCounting.forward_tendsto c).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=fourierL2 (E (compactFourier c h:Hq))))
  have right:=(tendsto_const_nhds (x:=E (sourceSB c:Hq))).inner (𝕜:=ℂ)
    ((fourierL2.continuous.tendsto _).comp (compact_fourier_forward_tendsto c h nn))
  have finite (N:ℕ) :inner ℂ (FiniteForcing.source N (E (sourceSB c:Hq))) (fourierL2 (E (compactFourier c h:Hq)))=
      inner ℂ (E (sourceSB c:Hq)) (fourierL2 (FiniteForcing.source N (E (compactFourier c h:Hq)))) :=by
    rw [CountingDual.source_pairing,KCounting.dual_fourier]
  have equation:=tendsto_nhds_unique (left.congr' (Eventually.of_forall finite)) right
  have positiveGap:=shifted_ambient_fourier_gap c h bound
  have negativeGap:=shifted_ambient_fourier_gap c (-h) (by linarith [Real.log_nonneg (by norm_num :(1:ℝ)≤2)])
  have shiftPair (t:ℝ) (gap:R (burnolMultiplicativeDilation t (fourierL2 (AmbientCounting.value c)))=0) :
      inner ℂ (E (sourceSB c:Hq)) (burnolMultiplicativeDilation t (fourierL2 (AmbientCounting.value c)))=0 :=by
    have adjoint:=ContinuousLinearMap.adjoint_inner_left R
      (burnolMultiplicativeDilation t (fourierL2 (AmbientCounting.value c))) (sourceSB c:Hq)
    change inner ℂ (E (sourceSB c:Hq)) (burnolMultiplicativeDilation t (fourierL2 (AmbientCounting.value c)))=_ at adjoint
    rw [adjoint,gap,inner_zero_right]
  have sourceGap:inner ℂ (E (sourceSB c:Hq)) (fourierL2 (AmbientCounting.value c))=0 :=by
    have adjoint:=ContinuousLinearMap.adjoint_inner_left R
      (fourierL2 (AmbientCounting.value c)) (sourceSB c:Hq)
    change inner ℂ (E (sourceSB c:Hq)) (fourierL2 (AmbientCounting.value c))=_ at adjoint
    rw [adjoint,AmbientFourier.original_fourier_gap,inner_zero_right]
  rw [equation,compactFourierForward,map_add,map_smul,map_smul,map_add,map_sub,
    fourierL2_burnolMultiplicativeDilation,fourierL2_burnolMultiplicativeDilation,neg_neg,
    inner_add_right,inner_smul_right,inner_smul_right,inner_add_right,inner_sub_right,
    shiftPair h positiveGap,shiftPair (-h) negativeGap,sourceGap,full_forward_fourier_pair c h nn bound]
  ring

private theorem counted_kernel_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    KCountingGram.value c=U c ConstantForward.value-fourierL2 (CountingDual.value c)+ReturnCounting.forwardValue c :=by
  have total:=((WholeGramSource.elementary_forward_tendsto c).sub
    ((fourierL2.continuous.tendsto _).comp (CountingDual.original_dual_tendsto c))).add (ReturnCounting.forward_tendsto c)
  have actual:Tendsto (fun N:ℕ=>FiniteForcing.source N (sourceKernel c)) atTop
      (𝓝 (U c ConstantForward.value-fourierL2 (CountingDual.value c)+ReturnCounting.forwardValue c)) :=by
    apply total.congr'
    filter_upwards [] with N
    change _=CountingDual.sourceCLM N (sourceKernel c)
    rw [sourceKernel,map_sub,map_add]
    simp only [CountingDual.sourceCLM_apply,forward_fourier,Function.comp_apply]
    change FiniteForcing.source N (elementarySource c)-fourierL2 (DualSource.source N (E (sourceB c:Hq)))+
      FiniteForcing.source N (E (sourceSB c:Hq))=FiniteForcing.source N (elementarySource c)+
      FiniteForcing.source N (E (sourceSB c:Hq))-fourierL2 (DualSource.source N (E (sourceB c:Hq)))
    module
  rw [sourceKernel_original] at actual
  exact tendsto_nhds_unique (KCountingGram.forward_tendsto c zero) actual

/-- Every term is generated by the original B compact words, actual unit-R field and original dual programme. -/
def compactFee (c:BurnolCompletedMellinCoordinate) (h:ℝ) :ℂ :=
  inner ℂ (U c ConstantForward.value) (compactCorrection c h)-star (sourceFourierMean (sourceB c))*
    inner ℂ ell (compactPosition c h)-inner ℂ (CountingDual.value c) (E (compactFourier c h:Hq))

theorem actual_compact_correction_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    inner ℂ (KCountingGram.value c) (compactCorrection c h)=compactFee c h :=by
  have position:=congrArg (fun value:M=>inner ℂ value (compactPosition c h)) (position_source c zero)
  have scaled (a:ℂ) (x y:M):inner ℂ (a • x) y=star a*inner ℂ x y :=inner_smul_left x y a
  rw [inner_sub_left,scaled,←projected_pair,←projected_pair] at position
  have fourier:inner ℂ (KCountingGram.value c) (fourierL2 (E (compactFourier c h:Hq)))=
      inner ℂ (U c ConstantForward.value) (fourierL2 (E (compactFourier c h:Hq)))-
        inner ℂ (CountingDual.value c) (E (compactFourier c h:Hq)) :=by
    rw [counted_kernel_source c zero,inner_add_left,inner_sub_left,fourierL2.inner_map_map,
      return_fourier_compact_zero c h nn bound,add_zero]
  rw [compactCorrection,inner_add_right,position,fourier]
  unfold compactFee compactCorrection
  rw [inner_add_right]
  ring
end OriginalKElementaryArithmeticAction.WholeWardCompactFee
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
