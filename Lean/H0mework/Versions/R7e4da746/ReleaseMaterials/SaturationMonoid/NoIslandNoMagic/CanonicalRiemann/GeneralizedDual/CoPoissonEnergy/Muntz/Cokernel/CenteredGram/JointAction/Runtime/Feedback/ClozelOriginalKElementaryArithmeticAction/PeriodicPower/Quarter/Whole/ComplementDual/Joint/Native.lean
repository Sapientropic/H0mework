import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierKernelDependentRAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFourierKernelDependentRAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa
open scoped Topology InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "E"=>burnolQuarterZeroExtension
local notation "Rq"=>burnolQuarterRestriction
local notation "T"=>burnolTateReciprocalL2
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "C"=>FiniteMobiusResolventFlux.cutoff q
local notation "leading"=>ForcingPrimitive.leadingCoefficient
local notation "B"=>burnolRieszSingleFourierSource
local notation "S"=>burnolMeanZeroTruncatedFourier

def nativeCompact (c:BurnolCompletedMellinCoordinate):Hq:=
  OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source.periodicQuarter c-(B c:Hq)

def nativeReturn (c:BurnolCompletedMellinCoordinate):BurnolL2:=
  leading c • fourierL2 (E (S (logBFirst c 0):Hq))-
    fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2)

/-- Both original B feet cancel before evolution, leaving the actual K and the one paid log return. -/
theorem actual_native_source (c:BurnolCompletedMellinCoordinate):
    jointSource c=E (nativeCompact c)+nativeReturn c:=by
  have original:=actual_original_FK_single_source c
  change fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2)=ForcingWhole.whole c+
    (fourierL2 (E (S (B c):Hq))-E (B c:Hq)) at original
  rw [jointSource,actual_original_dual_correction]
  simp only [Submodule.coe_sub,Submodule.coe_smul,map_sub,map_smul]
  unfold nativeCompact nativeReturn quarterWave
  rw [map_sub]
  linear_combination (norm:=module) original

private theorem rightQuarter (d:BurnolCompletedMellinCoordinate):1/4<(d.value/2).re:=by
  rw [Complex.div_re]
  norm_num
  linarith [d.rightHalf]

private theorem outgoing_compact (d:BurnolCompletedMellinCoordinate) (value:BurnolL2)
    (supported:C value=value):C (sourceVolterraResolvent d value)=sourceVolterraResolvent d value:=by
  have native:=OriginalPrimitiveRankBalance.cutoff_Rplus_source q (by norm_num) (d.value/2)
    (rightQuarter d) value
  rw [supported,FiniteMobiusResolventFlux.Rplus_tate _ (rightQuarter d)] at native
  exact native

private theorem outgoing_power_compact (d:BurnolCompletedMellinCoordinate) (state:Hq) (j:ℕ):
    C (((sourceVolterraResolvent d)^j) (E state))=((sourceVolterraResolvent d)^j) (E state):=by
  induction j with
  | zero =>
    change E (Rq (E state))=E state
    rw [burnolQuarterRestriction_zeroExtension]
  | succ j previous =>
    rw [pow_succ',mul_apply_eq_comp]
    exact outgoing_compact d _ previous

/-- The actual same-source outgoing recursion is the Tate conjugate of the complete original R iteration. -/
theorem actual_tate_outgoing (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    tateSource c j=((sourceVolterraResolvent (barC c))^j) (jointSource c):=by
  induction j with
  | zero => simp only [tateSource,directSource,pow_zero,one_apply_eq_self,burnolTateReciprocalL2_involutive]
  | succ j previous =>
    change T (((burnolDirectRightResolventCLM (barC c))^(j+1)) (T (jointSource c)))=_
    rw [pow_succ',mul_apply_eq_comp,pow_succ',mul_apply_eq_comp]
    simpa only [sourceVolterraResolvent,ContinuousLinearMap.comp_apply,tateSource,directSource,
      burnolTateReciprocalL2_involutive] using congrArg (sourceVolterraResolvent (barC c)) previous

private theorem compact_tail_zero (d:BurnolCompletedMellinCoordinate) (value:BurnolL2)
    (supported:C value=value):
    burnolRadiusMellinTailEvaluator 4 (by norm_num) d.value d.rightHalf value=0:=by
  rw [burnolRadiusMellinTailEvaluator_eq_integral]
  apply integral_eq_zero_of_ae
  have compact:=FiniteMobiusResolventFlux.cutoff_read q value
  rw [supported] at compact
  filter_upwards [ae_restrict_of_ae compact,ae_restrict_mem measurableSet_Ioi] with x source beyond
  change (4:ℝ)<x at beyond
  have outside:x∉symmetricInterval q:=by
    intro inside
    have positive:0<x:=lt_trans (by norm_num:(0:ℝ)<4) beyond
    have :=(abs_le.mpr inside)
    rw [abs_of_pos positive] at this
    linarith
  rw [source,indicator_of_notMem outside,mul_zero]
  rfl

/-- At every actual order the complete outgoing tail is generated solely by the original K/log source. -/
theorem actual_native_upper_tail (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    burnolRadiusMellinTailEvaluator 4 (by norm_num) (barC c).value (barC c).rightHalf (tateSource c j)=
      burnolRadiusMellinTailEvaluator 4 (by norm_num) (barC c).value (barC c).rightHalf
        (((sourceVolterraResolvent (barC c))^j) (nativeReturn c)):=by
  rw [actual_tate_outgoing,actual_native_source,map_add,map_add,
    compact_tail_zero (barC c) _ (outgoing_power_compact (barC c) (nativeCompact c) j),zero_add]

/-- This is the same actual original-m field consumed independently by the zero-owned K. -/
theorem actual_original_order_K_consumer (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner c.value
    inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2)
      (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa.directValue c zero h positive m)=
      inner ℂ (fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2))
        (residualValue c zero h positive (m-1)):=by
  dsimp only
  have orderPositive:=generatedRiemannXiZeroOrder_pos (burnolPaZeroObservation c zero)
    (burnolPaZeroObservation_nontrivial c zero)
  have orderNext:generatedRiemannXiZeroOrder ActualAnalyticOwner c.value-1+1=
      generatedRiemannXiZeroOrder ActualAnalyticOwner c.value:=by
    change 0<generatedRiemannXiZeroOrder ActualAnalyticOwner c.value at orderPositive
    omega
  simpa only [orderNext] using actual_original_K_consumer c zero h positive
    (generatedRiemannXiZeroOrder ActualAnalyticOwner c.value-1)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
