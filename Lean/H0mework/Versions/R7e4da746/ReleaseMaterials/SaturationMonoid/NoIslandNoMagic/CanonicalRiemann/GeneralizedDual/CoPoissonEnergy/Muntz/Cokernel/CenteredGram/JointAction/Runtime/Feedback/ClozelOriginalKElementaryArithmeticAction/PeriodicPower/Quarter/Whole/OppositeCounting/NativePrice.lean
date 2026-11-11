import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.JointContact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.NativeContact

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.NativePrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.NativeContact
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKDirectRCofinalOutsideVolterraSource
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Rq" => burnolQuarterRestriction
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "P0" => Constructor.zeroMean
local notation "μ" => burnolQuarterMeanCoefficient
local notation "C" => CenteredCountingDual.forward
local notation "B" => CenteredCountingDual.reverse
local notation "b" => burnolRieszSingleFourierSource

def returnWardPrice (N:ℕ) (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):ℂ :=
  inner ℂ (S (C N (b d))) (P0 (regularQuarter c zero))+
    inner ℂ (oppositeContact N (b d)) (P0 (regularQuarter c zero))+
    μ (regularQuarter c zero)*inner ℂ (Constructor.returnState d:Hq) SmallScaleLog.logL2

private theorem mean_pair (state:Hq):
    inner ℂ (intervalConstant q) state=μ state/2:=by
  unfold burnolQuarterMeanCoefficient
  rw [Complex.ofReal_pow,burnolIntervalConstant_norm_sq (by norm_num:(0:ℝ)<q)]
  norm_num
  ring

private theorem mean_zero_pair (left:M) (right:Hq):
    inner ℂ left (P0 right)=inner ℂ (left:Hq) right:=by
  change inner ℂ (left:Hq) (P0 right:Hq)=_
  rw [Constructor.zeroMean_read,inner_sub_right,inner_smul_right]
  have zero:inner ℂ (intervalConstant q) (left:Hq)=0:=
    (Submodule.mem_orthogonal _ _).mp left.property _ (Submodule.mem_span_singleton_self _)
  rw [inner_eq_zero_symm.mpr zero,mul_zero,sub_zero]

/-- The complete reverse native slot receives the two exterior actions and its actual logarithmic mean. -/
theorem actual_finite_return_ward_price (N:ℕ) (positive:0<N)
    (c d:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    inner ℂ (ReturnCounting.finite d N) (regularSource c zero)=returnWardPrice N c d zero:=by
  have source:inner ℂ (ReturnCounting.finite d N) (regularSource c zero)=
      inner ℂ (Rq (ReturnCounting.finite d N)) (regularQuarter c zero):=by
    calc
      _=inner ℂ (ReturnCounting.finite d N) (E (regularQuarter c zero)):=by
        rw [actual_regular_extension c zero]
      _=_:=ContinuousLinearMap.adjoint_inner_right Rq _ _
  have split:Rq (ReturnCounting.finite d N)=
      (P0 (Rq (ReturnCounting.finite d N)):Hq)+
        μ (Rq (ReturnCounting.finite d N)) • intervalConstant q:=by
    rw [Constructor.zeroMean_read]
    module
  have opposite:=actual_opposite_commutator N (b d)
  change B N (Constructor.returnState d)-S (C N (b d))=oppositeContact N (b d) at opposite
  have reversed:B N (Constructor.returnState d)=S (C N (b d))+oppositeContact N (b d):=by
    rw [←opposite]
    module
  rw [source,split,inner_add_left,inner_smul_left,mean_pair,
    ReturnCounting.finite_mean d N positive]
  simp only [starRingEnd_apply,star_mul,star_ofNat]
  rw [star_def,inner_conj_symm]
  change inner ℂ (B N (Constructor.returnState d):Hq) (regularQuarter c zero)+
    (inner ℂ (Constructor.returnState d:Hq) SmallScaleLog.logL2*2)*
      (μ (regularQuarter c zero)/2)=_
  rw [←mean_zero_pair,reversed,inner_add_left,returnWardPrice]
  ring

theorem actual_return_ward_price_limit (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    Tendsto (fun N:ℕ=>returnWardPrice N c d zero) atTop
      (𝓝 (inner ℂ (ReturnCounting.value d) (regularSource c zero))):=by
  have native:=(ReturnCounting.finite_tendsto d).inner (𝕜:=ℂ)
    (tendsto_const_nhds (x:=regularSource c zero))
  apply native.congr'
  filter_upwards [eventually_ge_atTop 1] with N bound
  exact actual_finite_return_ward_price N (by omega) c d zero

/-- The original combo is the limit of one complete same-N two-sided source price. -/
theorem actual_original_combo_ward_price_limit (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    Tendsto (fun N:ℕ=>
      star (jQuarterAmplitude d)*inner ℂ (gapState d) (wholeValue c zero h positive)-
      star (hQuarterAmplitude d)*inner ℂ (fourierL2 (gapState d)) (wholeValue c zero h positive)+
      star (jQuarterAmplitude d)*returnWardPrice N c d zero+
      star (hQuarterAmplitude d)*inner ℂ (DualSource.source N (E (b d:Hq))) (regularSource c zero))
      atTop (𝓝 (inner ℂ (sourceKernelCombo d) (wholeValue c zero h positive))):=by
  rw [actual_original_combo_native_price c d zero h positive]
  have first:=actual_return_ward_price_limit c d zero
  have second:=(CountingDual.original_dual_tendsto d).inner (𝕜:=ℂ)
    (tendsto_const_nhds (x:=regularSource c zero))
  exact ((tendsto_const_nhds.add (tendsto_const_nhds.mul first)).add
    (tendsto_const_nhds.mul second))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.NativePrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
