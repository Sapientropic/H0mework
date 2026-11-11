import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CompactMass
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open scoped Topology InnerProductSpace
open private outgoing_power_compact from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "E"=>burnolQuarterZeroExtension
local notation "Rq"=>burnolQuarterRestriction
local notation "Cq"=>intervalConstant q
local notation "μ"=>burnolQuarterMeanCoefficient
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate

private theorem rightQuarter (c:BurnolCompletedMellinCoordinate):1/4<(c.value/2).re:=by
  rw [Complex.div_re]
  norm_num
  linarith [c.rightHalf]

/-- The original adjoint computes the complete compact mass directly; its B(0) is unrestricted. -/
theorem actual_compact_mean_step (c:BurnolCompletedMellinCoordinate) (state:Hq):
    μ (Rq (sourceVolterraResolvent (barC c) (E state)))=(-2/star c.value)*μ state:=by
  have source:=sourceStep_actual c (E state)
  change (burnolDirectRightResolventCLM c).adjoint (E state)=
    sourceVolterraResolvent (barC c) (E state) at source
  have gap:Rq (E Cq)=(1:ℂ) • Cq:=by
    rw [burnolQuarterRestriction_zeroExtension,one_smul]
  have forward:=OriginalKForcingGapAction.right_resolvent_quarter_constant
    (c.value/2) (rightQuarter c) (E Cq) 1 gap
  have paired:inner ℂ Cq (Rq (sourceVolterraResolvent (barC c) (E state)))=
      (-2/star c.value)*inner ℂ Cq state:=by
    calc
      _=inner ℂ (E Cq) (sourceVolterraResolvent (barC c) (E state)):=by
        exact (ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ Cq).symm
      _=inner ℂ ((burnolDirectRightResolventCLM c) (E Cq)) (E state):=by
        rw [←source]
        exact ContinuousLinearMap.adjoint_inner_right _ _ _
      _=inner ℂ (Rq ((burnolDirectRightResolventCLM c) (E Cq))) state:=by
        exact ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction _ _
      _=_:=by
        change inner ℂ (Rq (burnolDirectRightResolvent (c.value/2) (E Cq))) state=_
        rw [forward,inner_smul_left]
        congr 1
        simp only [starRingEnd_apply,star_div₀,star_neg,star_one,star_ofNat]
        field_simp
  unfold burnolQuarterMeanCoefficient
  rw [paired]
  ring

/-- Every original outgoing iterate retains exactly its complete compact mass coefficient. -/
theorem actual_compact_mean_power (c:BurnolCompletedMellinCoordinate) (state:Hq) (j:ℕ):
    μ (Rq (((sourceVolterraResolvent (barC c))^j) (E state)))=
      (-2/star c.value)^j*μ state:=by
  induction j with
  | zero => simp only [pow_zero,one_apply_eq_self,burnolQuarterRestriction_zeroExtension,one_mul]
  | succ j previous =>
    have support:E (Rq (((sourceVolterraResolvent (barC c))^j) (E state)))=
        ((sourceVolterraResolvent (barC c))^j) (E state):=
      outgoing_power_compact (barC c) state j
    rw [pow_succ',mul_apply_eq_comp]
    conv_lhs=>rw [←support]
    rw [actual_compact_mean_step,previous,pow_succ]
    ring

private theorem native_mean (c:BurnolCompletedMellinCoordinate):
    μ (nativeCompact c)=μ (Rq (quarterWave c)):=by
  have zero:inner ℂ Cq (burnolRieszSingleFourierSource c:Hq)=0:=
    (Submodule.mem_orthogonal _ _).mp (burnolRieszSingleFourierSource c).property _
      (Submodule.mem_span_singleton_self _)
  rw [quarterWave,burnolQuarterRestriction_zeroExtension,nativeCompact]
  unfold burnolQuarterMeanCoefficient
  rw [inner_sub_right,zero,sub_zero]

/-- The actual joint compact stock carries H's ordinary mass at every order, including its complete B(0) cancellation. -/
theorem actual_native_compact_mean (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    μ (Rq (((sourceVolterraResolvent (barC c))^j) (E (nativeCompact c))))=
      (-2/star c.value)^j*μ (Rq (quarterWave c)):=by
  rw [actual_compact_mean_power,native_mean]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CompactMass
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
