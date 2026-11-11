import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mass
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.GammaBank
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Mean
open Complex ComplexConjugate Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKFiniteOrderRelease.QuarterSourceCommutator
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPower OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.PowerPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CountedXi
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field
open scoped Topology InnerProductSpace
open private constant_price from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPower
open private inward_restriction quarter_adjoint_left from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private pole_jet from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.GammaBank
local notation "q"=>(1/4:ℝ)
local notation "Rq"=>burnolQuarterRestriction
local notation "Cq"=>intervalConstant q
local notation "E"=>burnolQuarterZeroExtension
local notation "P"=>burnolEvenAmbientProjection
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "bare"=>generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner
local notation "μ"=>burnolQuarterMeanCoefficient

private def meanRead:BurnolL2→L[ℂ]ℂ:=(2:ℂ) • (innerSL ℂ Cq).comp Rq

private theorem mean_read (value:BurnolL2):meanRead value=μ (Rq value):=by
  change 2*inner ℂ Cq (Rq value)=_
  rw [constant_price]
  ring

private theorem zero_log (c d:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    inner ℂ (SingularCounting.powerL2 d) (Rq (fullFloorValue c zero))=
      2*mellin (fullFloorRaw c) d.value:=by
  have pair:=actual_log_pair d 0 (Rq (fullFloorValue c zero)) (fullFloorRaw c)
    (actual_floor_quarter_raw c zero) (actual_floor_even c.value c.belowOne)
  rw [actual_log_moment_jet c d zero 0] at pair
  simpa only [dividedLogColumn,Nat.factorial_zero,Nat.cast_one,div_one,Finset.sum_range_succ,
    Finset.sum_range_zero,zero_add,Nat.choose_zero_right,Nat.cast_one,Nat.sub_self,
    pow_zero,one_mul,mul_one,iteratedDeriv_zero] using pair

/-- The original inward/outward quarter adjunction computes its full mass and Mellin contact. -/
theorem actual_resolvent_mean (c d:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    meanRead (burnolDirectRightResolvent (d.value/2) (fullFloorValue c zero))=
      (2/(1-d.value))*μ (Rq (fullFloorValue c zero))-
        (8*(q:ℂ)^(1-d.value)/(1-d.value))*mellin (fullFloorRaw c) d.value:=by
  change 2*inner ℂ Cq (Rq (burnolDirectRightResolventCLM d (fullFloorValue c zero)))=_
  rw [inward_restriction,←quarter_adjoint_left,quarterStep_constant,
    inner_sub_left,inner_smul_left,inner_smul_left,constant_price,zero_log c d zero]
  have phase:star ((q:ℂ)^(1-star d.value))=(q:ℂ)^(1-d.value):=by
    have arg:(q:ℂ).arg≠Real.pi:=by
      rw [arg_ofReal_of_nonneg (by norm_num:q≥0)]
      exact ne_of_lt Real.pi_pos
    simpa only [star_def,map_sub,map_one,Complex.conj_ofReal]
      using (Complex.conj_cpow (q:ℂ) (1-d.value) arg).symm
  simp only [starRingEnd_apply,star_div₀,star_mul,star_sub,star_one,star_star,star_ofNat,phase]
  ring

private def tailMean (z:ℂ):ℂ:=8*(q:ℂ)^(1-z)/(1-z)

private theorem tailMean_analytic (c:BurnolCompletedMellinCoordinate):
    AnalyticAt ℂ tailMean (star c.value):=by
  have notOne:1-star c.value≠0:=by
    intro equal
    have part:=congrArg Complex.re equal
    simp only [sub_re,one_re,star_def,conj_re,zero_re] at part
    linarith [c.belowOne]
  have powered:AnalyticAt ℂ (fun z:ℂ=>(q:ℂ)^(1-z)) (star c.value):=
    (((differentiable_const (1:ℂ)).sub differentiable_id).const_cpow
      (Or.inl (by norm_num:(q:ℂ)≠0))).analyticAt _
  exact (analyticAt_const.mul powered).div (analyticAt_const.sub analyticAt_id) notOne

private theorem mellin_analytic (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    AnalyticAt ℂ (mellin (fullFloorRaw c)) (star c.value):=
  (((analyticAt_id.sub analyticAt_const).pow (order c.value-1)).mul
    (actual_complement_analytic c)).congr (actual_original_order_germ c zero).symm

private theorem leading_tail_product (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    iteratedDeriv (order c.value-1) (fun z:ℂ=>mellin (fullFloorRaw c) z*tailMean z)
      (star c.value)=((order c.value-1).factorial:ℂ)*bare (star c.value) (star c.value)/2*
        tailMean (star c.value):=by
  classical
  rw [iteratedDeriv_fun_mul (mellin_analytic c zero).contDiffAt (tailMean_analytic c).contDiffAt,
    Finset.sum_eq_single (order c.value-1)]
  · rw [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,iteratedDeriv_zero,actual_count_top_jet c zero]
  · intro i member different
    have before:i<order c.value-1:=by have:=Finset.mem_range.mp member;omega
    rw [actual_count_lower_jet c zero i before,mul_zero,zero_mul]
  · intro absent
    exact (absent (Finset.mem_range.mpr (by omega))).elim

private theorem mean_germ (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (fun z:ℂ=>meanRead (burnolDirectRightResolvent (z/2) (fullFloorValue c zero)))=ᶠ[𝓝 (star c.value)]
      (fun z:ℂ=>(2*μ (Rq (fullFloorValue c zero)))*(1-z)⁻¹-
        mellin (fullFloorRaw c) z*tailMean z):=by
  have right:∀ᶠz:ℂ in 𝓝 (star c.value),(1/2:ℝ)<z.re:=
    (continuous_re.tendsto (star c.value)).eventually (Ioi_mem_nhds
      (by simpa only [star_def,conj_re] using c.rightHalf))
  have below:∀ᶠz:ℂ in 𝓝 (star c.value),z.re<1:=
    (continuous_re.tendsto (star c.value)).eventually (Iio_mem_nhds
      (by simpa only [star_def,conj_re] using c.belowOne))
  filter_upwards [right,below] with z hr hb
  have source:=actual_resolvent_mean c ⟨z,hr,hb⟩ zero
  change meanRead (burnolDirectRightResolvent (z/2) (fullFloorValue c zero))=_ at source
  rw [source]
  unfold tailMean
  ring

theorem actual_power_mean (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    μ (Rq (powerValue c zero))=(2/(1-star c.value))^(order c.value)*μ (Rq (fullFloorValue c zero))+
      rieszAmplitude c*GapEuler.gapMean q c:=by
  have positive:0<order c.value:=generatedRiemannXiZeroOrder_pos
    (burnolPaZeroObservation c zero) (burnolPaZeroObservation_nontrivial c zero)
  have notOne:1-star c.value≠0:=by
    intro equal;have part:=congrArg Complex.re equal
    simp only [sub_re,one_re,star_def,conj_re,zero_re] at part
    linarith [c.belowOne]
  have native:iteratedDeriv (order c.value-1)
      (fun z:ℂ=>meanRead (burnolDirectRightResolvent (z/2) (fullFloorValue c zero))) (star c.value)=
      (((order c.value-1).factorial:ℂ)/(2:ℂ)^(order c.value-1))*μ (Rq (powerValue c zero)):=by
    have commute:iteratedDeriv (order c.value-1)
        (fun z:ℂ=>meanRead (burnolDirectRightResolvent (z/2) (fullFloorValue c zero))) (barC c).value=
        meanRead (iteratedDeriv (order c.value-1)
          (fun z:ℂ=>burnolDirectRightResolvent (z/2) (fullFloorValue c zero)) (barC c).value):=by
      change (iteratedFDeriv ℂ (order c.value-1)
        (meanRead ∘ (fun z:ℂ=>burnolDirectRightResolvent (z/2) (fullFloorValue c zero)))
        (barC c).value) (fun _=>1)=_
      rw [meanRead.iteratedFDeriv_comp_left
        ((OriginalRResolventParameterJet.parameter_analytic (barC c) (fullFloorValue c zero)).contDiffAt
          (n:=order c.value-1)) le_rfl]
      rfl
    rw [OriginalRResolventParameterJet.parameter_jet,map_smul,smul_eq_mul,
      show order c.value-1+1=order c.value by omega,mean_read] at commute
    exact commute
  have source:=(mean_germ c zero).iteratedDeriv_eq (order c.value-1)
  have first:ContDiffAt ℂ (order c.value-1)
      (fun z:ℂ=>(2*μ (Rq (fullFloorValue c zero)))*(1-z)⁻¹) (star c.value):=
    (contDiffAt_const.mul ((contDiffAt_const.sub contDiffAt_id).inv notOne))
  have second:ContDiffAt ℂ (order c.value-1)
      (fun z:ℂ=>mellin (fullFloorRaw c) z*tailMean z) (star c.value):=
    ((mellin_analytic c zero).mul (tailMean_analytic c)).contDiffAt
  rw [native,iteratedDeriv_fun_sub first second,iteratedDeriv_const_mul_field,pole_jet,
    leading_tail_product c zero,show order c.value-1+1=order c.value by omega] at source
  have factorial:((order c.value-1).factorial:ℂ)≠0:=by exact_mod_cast Nat.factorial_ne_zero _
  have rescaled:=congrArg (fun z:ℂ=>(2:ℂ)^(order c.value-1)/
    ((order c.value-1).factorial:ℂ)*z) source
  have gap:=GapEuler.gapMean_primitive q (by norm_num) c
  have qpower:(q:ℂ)^(1-star c.value)=(q:ℂ)*(q:ℂ)^(-star c.value):=by
    rw [show 1-star c.value=1+(-star c.value) by ring,
      Complex.cpow_add _ _ (by norm_num:(q:ℂ)≠0),Complex.cpow_one]
  have power:(2:ℂ)^(order c.value)=(2:ℂ)^(order c.value-1)*2:=by
    conv_lhs=>rw [show order c.value=(order c.value-1)+1 by omega]
    rw [pow_succ]
  unfold tailMean at rescaled
  rw [qpower] at rescaled
  unfold rieszAmplitude
  rw [div_pow,power]
  have gapValue:GapEuler.gapMean q c=(q:ℂ)^(-star c.value)/(2*(1-star c.value)):=by
    apply (eq_div_iff (mul_ne_zero (by norm_num) notOne)).mpr
    linear_combination 2*gap
  rw [gapValue]
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at rescaled ⊢
  field_simp [factorial,notOne] at rescaled ⊢
  linear_combination (1/8:ℂ)*rescaled

/-- The compact correction has exactly the original mass clock, with no discarded Unit. -/
theorem actual_compact_correction_mean (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    μ (compactCorrection c zero)=
      (2/(1-star c.value))^(order c.value)*μ (Rq (fullFloorValue c zero)):=by
  have elementary:μ (Rq (elementarySource c))=GapEuler.gapMean q c:=by
    change μ (Rq (gapState c))=_
    rw [gapState_restriction]
    have normalize:μ (GapEuler.gapMean q c • Cq)=2*inner ℂ Cq (GapEuler.gapMean q c • Cq):=by
      rw [constant_price]
      ring
    rw [normalize]
    rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
    change 2*(GapEuler.gapMean q c*(‖Cq‖:ℂ)^2)=_
    rw [burnolIntervalConstant_norm_sq (by norm_num:q>0)]
    norm_num
    ring
  have linear:μ (compactCorrection c zero)=
      μ (Rq (powerValue c zero))-rieszAmplitude c*μ (Rq (elementarySource c)):=by
    unfold OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field.compactCorrection
    rw [←mean_read (powerValue c zero-rieszAmplitude c • elementarySource c),
      map_sub,map_smul,smul_eq_mul,mean_read,mean_read]
  rw [linear,actual_power_mean c zero,elementary]
  ring

theorem actual_complete_power_physical_source (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    P (powerValue c zero)=rieszAmplitude c • burnolCompletedMellinRieszVector c+
      ((2/(1-star c.value))^(order c.value)*μ (Rq (fullFloorValue c zero))) • P ConstantDual.seed:=by
  rw [actual_power_physical_source c zero,actual_compact_correction_mean c zero]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Mean
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
