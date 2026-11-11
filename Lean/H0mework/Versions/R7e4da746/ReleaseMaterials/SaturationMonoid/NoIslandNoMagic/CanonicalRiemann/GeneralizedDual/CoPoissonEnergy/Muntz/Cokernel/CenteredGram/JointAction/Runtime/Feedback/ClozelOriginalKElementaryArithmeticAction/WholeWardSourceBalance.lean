import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeBForcingSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeGramSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.WholeWardSourceBalance
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open OriginalKExteriorCoPoissonAction WholeBForcingSource
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "C" => ConstantDual.seed

/-- Both terms belong to the actual second B drive and its retained original forcing. -/
def outwardB (c:BurnolCompletedMellinCoordinate) (h:ℝ) : M :=
  sourceSecondSB c h+meanZeroDilation (-h) (sourceEta c)
def compactReturn (c:BurnolCompletedMellinCoordinate) (h:ℝ) : M :=
  sourceFirstSB c h-S (outwardB c h)

private theorem outward_actual (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    outwardB c h=meanZeroDilation (-h) (sourceB c) :=sourceSecondSB_actual c h nn

private theorem outward_extension (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    E (outwardB c h:Hq)=burnolMultiplicativeDilation (-h) (E (sourceB c:Hq))-FullUnit.fullSource c h 0 :=by
  rw [outward_actual c h nn,outward_full_source_inventory]
  change _=_-fullWindowLoss h (sourceB c)
  module

/-- This whole word retains its actual Fourier loss and its complete compact correction. -/
theorem outward_whole_source_word (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    WholeBForcingSource.sourceCorrection (outwardB c h)=burnolMultiplicativeDilation h (WholeBForcingSource.sourceCorrection (sourceB c))-
      fourierL2 (FullUnit.fullSource c h 0)+E (compactReturn c h:Hq) :=by
  unfold WholeBForcingSource.sourceCorrection compactReturn
  rw [outward_extension c h nn,map_sub,fourierL2_burnolMultiplicativeDilation,neg_neg]
  simp only [map_sub,Submodule.coe_sub]
  rw [sourceFirstSB_actual c h nn,inward_extension h nn]
  simp only [sourceSB]
  module

private theorem reverse_pair (N:ℕ) (left right:BurnolL2) :
    inner ℂ (DualSource.source N left) right=inner ℂ left (FiniteForcing.source N right) :=by
  rw [CountingDual.dual_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left (CountingDual.sourceCLM N) _ _

private theorem dual_dilation (N:ℕ) (h:ℝ) (value:BurnolL2) :
    DualSource.source N (burnolMultiplicativeDilation h value)=burnolMultiplicativeDilation h (DualSource.source N value) :=by
  apply ext_inner_right ℂ
  intro test
  have flip (x y:BurnolL2) : inner ℂ (burnolMultiplicativeDilation h x) y=inner ℂ x (burnolMultiplicativeDilation (-h) y) :=by
    have actual:=(burnolMultiplicativeDilation h).inner_map_eq_flip x y
    rwa [←burnolMultiplicativeDilation_neg_eq_symm] at actual
  calc
    _=inner ℂ (burnolMultiplicativeDilation h value) (FiniteForcing.source N test) :=reverse_pair _ _ _
    _=inner ℂ value (burnolMultiplicativeDilation (-h) (FiniteForcing.source N test)) :=flip _ _
    _=inner ℂ value (FiniteForcing.source N (burnolMultiplicativeDilation (-h) test)) :=by rw [SeedCounting.source_dilation]
    _=inner ℂ (DualSource.source N value) (burnolMultiplicativeDilation (-h) test) :=(reverse_pair _ _ _).symm
    _=_ :=(flip _ _).symm

private theorem correction_supported_pair (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (value:M) :
    inner ℂ (elementaryReverseSource c zero) (WholeBForcingSource.sourceCorrection value)=
      sourceFourierMean value*inner ℂ (elementaryReverseSource c zero) C :=by
  have supported:=elementary_reverse_support c zero
  change E (R (elementaryReverseSource c zero))=elementaryReverseSource c zero at supported
  have gap:R (WholeBForcingSource.sourceCorrection value)=sourceFourierMean value • intervalConstant q :=by
    rw [WholeBForcingSource.sourceCorrection,map_sub,burnolQuarterRestriction_zeroExtension,
      burnolMeanZeroTruncatedFourier_coe,burnolMeanZeroProjection_eq_sub_constant]
    change burnolTruncatedFourier (value:Hq)-(burnolTruncatedFourier (value:Hq)-
      sourceFourierMean value • intervalConstant q)=_
    module
  calc
    _=inner ℂ (R (elementaryReverseSource c zero)) (R (WholeBForcingSource.sourceCorrection value)) :=by
      conv_lhs=>lhs; rw [←supported]
      exact ContinuousLinearMap.adjoint_inner_left R _ _
    _=sourceFourierMean value*inner ℂ (R (elementaryReverseSource c zero)) (intervalConstant q) :=by rw [gap,inner_smul_right]
    _=_ :=by
      congr 1
      exact (ContinuousLinearMap.adjoint_inner_right R _ _).symm

/-- The whole reciprocal loss is a source input of this price; no output projection is discarded. -/
def outwardForcingPrice (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) : ℂ :=
  sourceFourierMean (outwardB c h)*(inner ℂ (elementaryReverseSource c zero) C+
    inner ℂ (sourceSB c:Hq) SmallScaleLog.logL2)-
    inner ℂ (E (sourceB c:Hq)) (burnolMultiplicativeDilation (-h) (CountingDual.value c)-FullUnit.fullReverse c h 0)

theorem outward_whole_forcing_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) (nn:0≤h) :
    Tendsto (fun N:ℕ=>inner ℂ (sourceKernel c) (FiniteForcing.source N (WholeBForcingSource.sourceCorrection (outwardB c h)))) atTop
      (𝓝 (outwardForcingPrice c zero h)) :=by
  have first:=(elementary_reverse_tendsto c zero).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=WholeBForcingSource.sourceCorrection (outwardB c h)))
  rw [correction_supported_pair] at first
  have input:Tendsto (fun N:ℕ=>DualSource.source N (E (outwardB c h:Hq))) atTop
      (𝓝 (burnolMultiplicativeDilation (-h) (CountingDual.value c)-FullUnit.fullReverse c h 0)) :=by
    have actual:=(((burnolMultiplicativeDilation (-h)).continuous.tendsto _).comp (CountingDual.original_dual_tendsto c)).sub
      (FullUnit.full_reverse_tendsto c h nn 0)
    apply actual.congr'
    filter_upwards [] with N
    rw [outward_extension c h nn]
    have linear:DualSource.source N (burnolMultiplicativeDilation (-h) (E (sourceB c:Hq))-FullUnit.fullSource c h 0)=
        DualSource.source N (burnolMultiplicativeDilation (-h) (E (sourceB c:Hq)))-DualSource.source N (FullUnit.fullSource c h 0) :=by
      simp only [CountingDual.dual_eq_adjoint,map_sub]
    rw [linear,dual_dilation]
    rfl
  have second:=(tendsto_const_nhds (x:=E (sourceB c:Hq))).inner (𝕜:=ℂ) input
  have tail:=original_mixed_cotest_tendsto_zero c (S (outwardB c h):Hq)
  have tail':Tendsto (fun N:ℕ=>inner ℂ (fourierL2 (FiniteForcing.source N (E (sourceB c:Hq)))) (E (S (outwardB c h):Hq))) atTop (𝓝 0) :=
    tail.congr' (Eventually.of_forall (fun N=>original_mixed_cotest c N _))
  have total:=((first.sub second).add_const (sourceFourierMean (outwardB c h)*inner ℂ (sourceSB c:Hq) SmallScaleLog.logL2)).add tail'
  have totalValue:sourceFourierMean (outwardB c h)*inner ℂ (elementaryReverseSource c zero) C-
      inner ℂ (E (sourceB c:Hq)) (burnolMultiplicativeDilation (-h) (CountingDual.value c)-FullUnit.fullReverse c h 0)+
      sourceFourierMean (outwardB c h)*inner ℂ (sourceSB c:Hq) SmallScaleLog.logL2+0=outwardForcingPrice c zero h :=by
    unfold outwardForcingPrice
    ring
  rw [totalValue] at total
  apply total.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N after
  exact (finite_whole_source_price c N (Nat.lt_of_lt_of_le (by decide:0<1) after) (outwardB c h)).symm

private theorem tate_dual_gap (c:BurnolCompletedMellinCoordinate) :R (burnolTateReciprocalL2 (CountingDual.value c))=0 :=by
  rw [DualLanding.original_tate_fourier,burnolTateReciprocalL2_involutive,AmbientFourier.original_fourier_gap]

private theorem compact_forward_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (value:M) :
    Tendsto (fun N:ℕ=>inner ℂ (sourceKernel c) (FiniteForcing.source N (E (value:Hq)))) atTop
      (𝓝 (-inner ℂ (PositionCounting.value c zero) (E (value:Hq)))) :=by
  have actual:=(KCounting.original_tendsto c zero).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=E (value:Hq)))
  have tate:inner ℂ (burnolTateReciprocalL2 (CountingDual.value c)) (E (value:Hq))=0 :=by
    have adjoint:=ContinuousLinearMap.adjoint_inner_right R (burnolTateReciprocalL2 (CountingDual.value c)) (value:Hq)
    change inner ℂ (burnolTateReciprocalL2 (CountingDual.value c)) (E (value:Hq))=_ at adjoint
    rw [adjoint,tate_dual_gap,inner_zero_left]
  rw [inner_sub_left,inner_neg_left,tate,sub_zero] at actual
  apply actual.congr'
  filter_upwards [] with N
  rw [reverse_pair,sourceKernel_original]

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

def negativeBasePrice (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) :ℂ :=
  outwardForcingPrice c zero h+inner ℂ (sourceKernel c) (fourierL2 (FullUnit.fullReverse c h 0))+
    inner ℂ (PositionCounting.value c zero) (E (compactReturn c h:Hq))

/-- The compact return has its actual counted price; its uncounted K-orthogonality is not reused. -/
theorem negative_base_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) (nn:0≤h) :
    Tendsto (fun N:ℕ=>inner ℂ (sourceKernel c) (burnolMultiplicativeDilation h
      (FiniteForcing.source N (WholeBForcingSource.sourceCorrection (sourceB c))))) atTop (𝓝 (negativeBasePrice c zero h)) :=by
  have first:=outward_whole_forcing_price c zero h nn
  have second:=(tendsto_const_nhds (x:=sourceKernel c)).inner (𝕜:=ℂ)
    ((fourierL2.continuous.tendsto _).comp (FullUnit.full_reverse_tendsto c h nn 0))
  have third:=compact_forward_price c zero (compactReturn c h)
  have total:=(first.add second).sub third
  have totalValue:outwardForcingPrice c zero h+inner ℂ (sourceKernel c) (fourierL2 (FullUnit.fullReverse c h 0))-
      -inner ℂ (PositionCounting.value c zero) (E (compactReturn c h:Hq))=negativeBasePrice c zero h :=by
    unfold negativeBasePrice
    ring
  rw [totalValue] at total
  apply total.congr'
  filter_upwards [] with N
  have word:=congrArg (fun value:BurnolL2=>CountingDual.sourceCLM N value) (outward_whole_source_word c h nn)
  rw [map_add,map_sub] at word
  simp only [CountingDual.sourceCLM_apply,SeedCounting.source_dilation,forward_fourier] at word
  have price:=congrArg (inner ℂ (sourceKernel c)) word
  rw [inner_add_right,inner_sub_right] at price
  simp only [Function.comp_apply]
  linear_combination price

/-- Both the original Rbar unit field and every retained loss fee remain in the negative shift. -/
theorem counted_kernel_negative_shift (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) (nn:0≤h) :
    inner ℂ (burnolMultiplicativeDilation (-h) (sourceKernel c)) (KCountingGram.value c)=
      inner ℂ (burnolMultiplicativeDilation (-h) (sourceKernel c)) (unitResolventSource c ConstantForward.value)-negativeBasePrice c zero h :=by
  have first:=((burnolMultiplicativeDilation h).continuous.tendsto _).comp (WholeGramSource.elementary_forward_tendsto c)
  have second:=((burnolMultiplicativeDilation h).continuous.tendsto _).comp (KCountingGram.forward_tendsto c zero)
  have actual:=(tendsto_const_nhds (x:=sourceKernel c)).inner (𝕜:=ℂ) (first.sub second)
  have finite:Tendsto (fun N:ℕ=>inner ℂ (sourceKernel c) (burnolMultiplicativeDilation h
      (FiniteForcing.source N (WholeBForcingSource.sourceCorrection (sourceB c))))) atTop
      (𝓝 (inner ℂ (sourceKernel c) (burnolMultiplicativeDilation h (unitResolventSource c ConstantForward.value)-
        burnolMultiplicativeDilation h (KCountingGram.value c)))) :=by
    apply actual.congr'
    filter_upwards [] with N
    have source:WholeBForcingSource.sourceCorrection (sourceB c)=elementarySource c-sourceKernel c :=by
      unfold WholeBForcingSource.sourceCorrection sourceKernel sourceSB
      module
    rw [source]
    change _=inner ℂ (sourceKernel c) (burnolMultiplicativeDilation h
      (CountingDual.sourceCLM N (elementarySource c-sourceKernel c)))
    rw [map_sub,map_sub,sourceKernel_original]
    rfl
  have equation:=tendsto_nhds_unique finite (negative_base_price c zero h nn)
  have flip (value:BurnolL2):inner ℂ (burnolMultiplicativeDilation (-h) (sourceKernel c)) value=
      inner ℂ (sourceKernel c) (burnolMultiplicativeDilation h value) :=by
    have read:=(burnolMultiplicativeDilation (-h)).inner_map_eq_flip (sourceKernel c) value
    rwa [←burnolMultiplicativeDilation_neg_eq_symm,neg_neg] at read
  rw [inner_sub_right,←flip,←flip] at equation
  linear_combination -equation
end OriginalKElementaryArithmeticAction.WholeWardSourceBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
