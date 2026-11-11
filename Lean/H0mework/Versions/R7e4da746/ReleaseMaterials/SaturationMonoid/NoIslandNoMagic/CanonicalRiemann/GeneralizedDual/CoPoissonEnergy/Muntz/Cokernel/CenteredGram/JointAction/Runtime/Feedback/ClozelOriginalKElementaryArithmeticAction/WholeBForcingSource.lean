import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.BCountingCocycle
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.WholeBForcingSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open OriginalKExteriorCoPoissonAction BCountingCocycle
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "C" => ConstantDual.seed

def sourceCorrection (value:M) : BurnolL2 := fourierL2 (E (value:Hq))-E (S value:Hq)
def sourceFourierMean (value:M) : ℂ := burnolQuarterMeanCoefficient (burnolTruncatedFourier (value:Hq))

private theorem reverse_pair (N:ℕ) (left right:BurnolL2) :
    inner ℂ (DualSource.source N left) right=inner ℂ left (FiniteForcing.source N right) := by
  rw [CountingDual.dual_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left (CountingDual.sourceCLM N) _ _

private theorem source_B_even (c:BurnolCompletedMellinCoordinate) : reflectL2 (E (sourceB c:Hq))=E (sourceB c:Hq) := by
  change reflectL2 (burnolRadiusZeroExtension q (sourceB c:Hq))=_
  have even:reflectRestricted q (sourceB c:Hq)=sourceB c :=burnolRieszSingleFourierSource_reflection_fixed c
  rw [burnolRadiusZeroExtension_reflect,even]
  rfl

/-- The mixed finite operator is read on its original b source before the limit. -/
theorem original_mixed_cotest (c:BurnolCompletedMellinCoordinate) (N:ℕ) (value:Hq) :
    inner ℂ (E (sourceB c:Hq)) (fourierL2 (FiniteForcing.source N (E value)))=
      inner ℂ (fourierL2 (FiniteForcing.source N (E (sourceB c:Hq)))) (E value) := by
  have swap:=fourierL2.inner_map_map (fourierL2 (E (sourceB c:Hq))) (FiniteForcing.source N (E value))
  rw [fourierL2_fourierL2,source_B_even] at swap
  rw [swap,←reverse_pair,KCounting.dual_fourier]

/-- The paid original forward-b Fourier gap removes the complete mixed price, including its exterior. -/
theorem original_mixed_cotest_tendsto_zero (c:BurnolCompletedMellinCoordinate) (value:Hq) :
    Tendsto (fun N:ℕ=>inner ℂ (E (sourceB c:Hq)) (fourierL2 (FiniteForcing.source N (E value)))) atTop (𝓝 0) := by
  have actual:=((fourierL2.continuous.tendsto _).comp (AmbientCounting.original_ambient_limit c)).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=E value))
  have price:inner ℂ (fourierL2 (AmbientCounting.value c)) (E value)=0 := by
    have adjoint:=ContinuousLinearMap.adjoint_inner_right R (fourierL2 (AmbientCounting.value c)) value
    change inner ℂ (fourierL2 (AmbientCounting.value c)) (E value)=
      inner ℂ (R (fourierL2 (AmbientCounting.value c))) value at adjoint
    rw [adjoint,AmbientFourier.original_fourier_gap,inner_zero_left]
  rw [price] at actual
  exact actual.congr' (Eventually.of_forall (fun N=>(original_mixed_cotest c N value).symm))

private theorem correction_gap (value:M) : R (sourceCorrection value)=sourceFourierMean value • intervalConstant q := by
  rw [sourceCorrection,map_sub,burnolQuarterRestriction_zeroExtension,
    burnolMeanZeroTruncatedFourier_coe,burnolMeanZeroProjection_eq_sub_constant]
  change burnolTruncatedFourier (value:Hq)-(burnolTruncatedFourier (value:Hq)-
    sourceFourierMean value • intervalConstant q)=_
  module

private theorem supported_correction_pair (value:BurnolL2) (supported:value=E (R value)) (test:M) :
    inner ℂ value (sourceCorrection test)=sourceFourierMean test*inner ℂ value C := by
  calc
    _=inner ℂ (R value) (R (sourceCorrection test)) := by
      conv_lhs=>lhs; rw [supported]
      exact ContinuousLinearMap.adjoint_inner_left R _ _
    _=sourceFourierMean test*inner ℂ (R value) (intervalConstant q) := by rw [correction_gap,inner_smul_right]
    _=_ := by
      congr 1
      exact (ContinuousLinearMap.adjoint_inner_right R value (intervalConstant q)).symm

private theorem return_finite_unit (c:BurnolCompletedMellinCoordinate) (N:ℕ) (positive:0<N) :
    inner ℂ (DualSource.source N (E (sourceSB c:Hq))) C=inner ℂ (sourceSB c:Hq) SmallScaleLog.logL2 := by
  rw [reverse_pair]
  change inner ℂ (E (sourceSB c:Hq)) (FiniteForcing.source N (E (intervalConstant q)))=_
  have adjoint:=ContinuousLinearMap.adjoint_inner_left R
    (FiniteForcing.source N (E (intervalConstant q))) (sourceSB c:Hq)
  change inner ℂ (E (sourceSB c:Hq)) (FiniteForcing.source N (E (intervalConstant q)))=
    inner ℂ (sourceSB c:Hq) (WindowCounting.windowSource N (intervalConstant q)) at adjoint
  rw [adjoint,WindowCounting.constant_source N positive,inner_add_right,inner_smul_right]
  have mean:inner ℂ (sourceSB c:Hq) (intervalConstant q)=0 :=
    inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp (sourceSB c).property _ (Submodule.mem_span_singleton_self _))
  rw [mean,mul_zero,zero_add]

/-- All finite mean terms are retained until their same-source cancellation. -/
theorem finite_whole_source_price (c:BurnolCompletedMellinCoordinate) (N:ℕ) (positive:0<N) (value:M) :
    inner ℂ (sourceKernel c) (FiniteForcing.source N (sourceCorrection value))=
      inner ℂ (DualSource.source N (elementarySource c)) (sourceCorrection value)-
        inner ℂ (E (sourceB c:Hq)) (DualSource.source N (E (value:Hq)))+
        sourceFourierMean value*inner ℂ (sourceSB c:Hq) SmallScaleLog.logL2+
        inner ℂ (fourierL2 (FiniteForcing.source N (E (sourceB c:Hq)))) (E (S value:Hq)) := by
  have inventory:DualSource.source N (sourceKernel c)=DualSource.source N (elementarySource c)-
      (fourierL2 (FiniteForcing.source N (E (sourceB c:Hq)))-DualSource.source N (E (sourceSB c:Hq))) := by
    rw [sourceKernel,CountingDual.dual_eq_adjoint,map_sub,map_add]
    simp only [←CountingDual.dual_eq_adjoint,KCounting.dual_fourier]
    module
  have supported:DualSource.source N (E (sourceSB c:Hq))=E (R (DualSource.source N (E (sourceSB c:Hq)))) :=
    CenteredCountingDualSupport.source_support (sourceSB c) (burnolRieszSingleFourierReturn_reflection_fixed c) N positive
  have contact:=supported_correction_pair _ supported value
  rw [return_finite_unit c N positive] at contact
  rw [←reverse_pair,inventory,inner_sub_left,inner_sub_left,contact]
  simp only [sourceCorrection,inner_sub_right,fourierL2.inner_map_map,CountingDual.source_pairing]
  ring

private theorem dual_dilation (N:ℕ) (h:ℝ) (value:BurnolL2) :
    DualSource.source N (burnolMultiplicativeDilation h value)=
      burnolMultiplicativeDilation h (DualSource.source N value) := by
  apply ext_inner_right ℂ
  intro test
  have flip (x y:BurnolL2) : inner ℂ (burnolMultiplicativeDilation h x) y=inner ℂ x (burnolMultiplicativeDilation (-h) y) := by
    have actual:=(burnolMultiplicativeDilation h).inner_map_eq_flip x y
    rwa [←burnolMultiplicativeDilation_neg_eq_symm] at actual
  calc
    _=inner ℂ (burnolMultiplicativeDilation h value) (FiniteForcing.source N test) :=reverse_pair _ _ _
    _=inner ℂ value (burnolMultiplicativeDilation (-h) (FiniteForcing.source N test)) :=flip _ _
    _=inner ℂ value (FiniteForcing.source N (burnolMultiplicativeDilation (-h) test)) :=by rw [SeedCounting.source_dilation]
    _=inner ℂ (DualSource.source N value) (burnolMultiplicativeDilation (-h) test) :=(reverse_pair _ _ _).symm
    _=_ :=(flip _ _).symm

private theorem original_return_unit_price (c:BurnolCompletedMellinCoordinate) :
    inner ℂ (ReturnCounting.value c) C=inner ℂ (sourceSB c:Hq) SmallScaleLog.logL2 := by
  have actual:=(ReturnCounting.finite_tendsto c).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=C))
  have generated:Tendsto (fun N:ℕ=>inner ℂ (ReturnCounting.finite c N) C) atTop
      (𝓝 (inner ℂ (sourceSB c:Hq) SmallScaleLog.logL2)) :=by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N after
    exact (return_finite_unit c N (Nat.lt_of_lt_of_le (by decide:0<1) after)).symm
  exact tendsto_nhds_unique actual generated

/-- The original source position count and actual B dilation are the only inputs of the price. -/
def sourceForcingPrice (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) : ℂ :=
  -sourceFourierMean (sourceFirstB c h)*inner ℂ (PositionCounting.value c zero) C-
    inner ℂ (E (sourceB c:Hq)) (burnolMultiplicativeDilation h (CountingDual.value c))

theorem whole_source_forcing_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) :
    Tendsto (fun N:ℕ=>inner ℂ (sourceKernel c) (FiniteForcing.source N (sourceCorrection (sourceFirstB c h))))
      atTop (𝓝 (sourceForcingPrice c zero h)) := by
  have first:=((elementary_reverse_tendsto c zero).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=sourceCorrection (sourceFirstB c h))))
  have supported:(elementaryReverseSource c zero)=E (R (elementaryReverseSource c zero)) := by
    have actual:=elementary_reverse_support c zero
    change E (R (elementaryReverseSource c zero))=elementaryReverseSource c zero at actual
    exact actual.symm
  rw [supported_correction_pair _ supported] at first
  have input:Tendsto (fun N:ℕ=>DualSource.source N (E (sourceFirstB c h:Hq))) atTop
      (𝓝 (burnolMultiplicativeDilation h (CountingDual.value c))) := by
    have actual:=((burnolMultiplicativeDilation h).continuous.tendsto _).comp (CountingDual.original_dual_tendsto c)
    apply actual.congr'
    filter_upwards [] with N
    rw [sourceFirstB_actual c h nn,inward_extension h nn,dual_dilation]
    rfl
  have second:=(tendsto_const_nhds (x:=E (sourceB c:Hq))).inner (𝕜:=ℂ) input
  have tail:=original_mixed_cotest_tendsto_zero c (S (sourceFirstB c h):Hq)
  have tail':Tendsto (fun N:ℕ=>inner ℂ (fourierL2 (FiniteForcing.source N (E (sourceB c:Hq)))) (E (S (sourceFirstB c h):Hq))) atTop (𝓝 0) :=
    tail.congr' (Eventually.of_forall (fun N=>original_mixed_cotest c N _))
  have total:=((first.sub second).add_const (sourceFourierMean (sourceFirstB c h)*inner ℂ (sourceSB c:Hq) SmallScaleLog.logL2)).add tail'
  simp only [add_zero] at total
  have totalValue:sourceFourierMean (sourceFirstB c h)*inner ℂ (elementaryReverseSource c zero) C-
      inner ℂ (E (sourceB c:Hq)) (burnolMultiplicativeDilation h (CountingDual.value c))+
      sourceFourierMean (sourceFirstB c h)*inner ℂ (sourceSB c:Hq) SmallScaleLog.logL2=sourceForcingPrice c zero h :=by
    unfold sourceForcingPrice elementaryReverseSource
    rw [inner_sub_left,inner_neg_left,original_return_unit_price]
    ring
  rw [totalValue] at total
  apply total.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N after
  have price:=finite_whole_source_price c N (Nat.lt_of_lt_of_le (by decide:0<1) after) (sourceFirstB c h)
  exact price.symm
end OriginalKElementaryArithmeticAction.WholeBForcingSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
