import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.ActedSchur
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ArithmeticLogGram

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.PlainLog
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace
open private quarter_profile from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction
local notation "q"=>(1/4:ℝ)
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "Cq"=>intervalConstant q
local notation "ell"=>CenteredCountingDual.logarithm
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate

private def plainRaw (t:ℝ):ℂ:=(Real.log t:ℂ)-(Real.log q:ℂ)+1
private def primitive (c:BurnolCompletedMellinCoordinate) (t:ℝ):ℂ:=
  (t:ℂ)^(1-c.value)*(plainRaw t/(1-c.value)-1/(1-c.value)^2)
private theorem denominator (c:BurnolCompletedMellinCoordinate):1-c.value≠0:=by
  intro h
  have real:=congrArg Complex.re h
  simp only [sub_re,one_re,zero_re] at real
  linarith [c.belowOne]

private theorem primitive_derivative (c:BurnolCompletedMellinCoordinate) (t:ℝ) (positive:0<t):
    HasDerivAt (primitive c) ((t:ℂ)^(-c.value)*plainRaw t) t:=by
  have power:=hasDerivAt_ofReal_cpow_const positive.ne' (denominator c)
  have logarithm:HasDerivAt (fun u:ℝ=>(Real.log u:ℂ)) ((t:ℂ)⁻¹) t:=by
    have rawderiv:=(Complex.ofRealCLM.hasFDerivAt : HasFDerivAt (fun u:ℝ=>(u:ℂ)) Complex.ofRealCLM (Real.log t)).comp_hasDerivAt t
      (Real.hasDerivAt_log positive.ne')
    change HasDerivAt (fun u:ℝ=>(Real.log u:ℂ)) ((t⁻¹:ℝ):ℂ) t at rawderiv
    simpa only [Complex.ofReal_inv] using rawderiv
  have read:HasDerivAt plainRaw ((t:ℂ)⁻¹) t:=
    (logarithm.sub_const (Real.log q:ℂ)).add_const 1
  have inversePower:(t:ℂ)^(1-c.value)*(t:ℂ)⁻¹=(t:ℂ)^(-c.value):=by
    rw [←Complex.cpow_neg_one,←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
    congr 1
    ring
  have generated:HasDerivAt (primitive c)
      (((1-c.value)*(t:ℂ)^(1-c.value-1))*(plainRaw t/(1-c.value)-1/(1-c.value)^2)+
        (t:ℂ)^(1-c.value)*((t:ℂ)⁻¹/(1-c.value))) t:=
    power.mul ((read.div_const (1-c.value)).sub_const (1/(1-c.value)^2))
  convert generated using 1
  rw [show 1-c.value-1= -c.value by ring]
  have regroup:(t:ℂ)^(1-c.value)*((t:ℂ)⁻¹/(1-c.value))=
      ((t:ℂ)^(1-c.value)*(t:ℂ)⁻¹)/(1-c.value):=by ring
  rw [regroup,inversePower]
  field_simp [denominator c]
  ring

private theorem plain_integral (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x) (small:x≤q):
    (∫t:ℝ in x..q,(t:ℂ)^(-c.value)*plainRaw t)=primitive c q-primitive c x:=by
  have regular:ContinuousOn (fun t:ℝ=>(t:ℂ)^(-c.value)*plainRaw t) (Icc x q):=by
    apply ContinuousOn.mul
    · intro t inside
      exact (continuousAt_ofReal_cpow_const t (-c.value) (Or.inr (ne_of_gt (positive.trans_le inside.1)))).continuousWithinAt
    · intro t inside
      exact (((Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log (ne_of_gt (positive.trans_le inside.1)))).sub continuousAt_const).add
        continuousAt_const).continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (regular.intervalIntegrable_of_Icc small)
  intro t inside
  have located:t∈Icc x q:=by simpa only [uIcc_of_le small] using inside
  exact primitive_derivative c t (positive.trans_le located.1)

private theorem plain_read : (ell:ℝ→ℂ)=ᵐ[μq]plainRaw:=by
  apply ArithmeticLogGram.logarithm_coeFn.trans
  filter_upwards with x
  simp only [plainRaw,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_one]

private theorem plain_even:reflectRestricted q (ell:Hq)=(ell:Hq):=by
  apply Lp.ext
  have moved:=(negMeasurePreserving_restrict q).quasiMeasurePreserving.ae plain_read
  filter_upwards [Lp.coeFn_compMeasurePreserving (ell:Hq) (negMeasurePreserving_restrict q),plain_read,moved]
    with x reflection direct reverse
  change reflectRestricted q (ell:Hq) x=(ell:Hq) (-x) at reflection
  rw [reflection,direct,reverse]
  simp only [plainRaw,Real.log_neg_eq_log]

private theorem plain_quarter (c:BurnolCompletedMellinCoordinate):
    quarterStep (barC c) (ell:Hq)=
      (2/(1-c.value)) • (ell:Hq)-(2/(1-c.value)^2) • Cq+
      (2*c.value*(q:ℂ)^(1-c.value)/(1-c.value)^2) • SingularCounting.powerL2 (barC c):=by
  have read:=quarter_profile (barC c) (ell:Hq) plainRaw plain_even plain_read
  apply Lp.ext
  filter_upwards [read,Lp.coeFn_add
      ((2/(1-c.value)) • (ell:Hq)-(2/(1-c.value)^2) • Cq)
      ((2*c.value*(q:ℂ)^(1-c.value)/(1-c.value)^2) • SingularCounting.powerL2 (barC c)),
    Lp.coeFn_sub ((2/(1-c.value)) • (ell:Hq)) ((2/(1-c.value)^2) • Cq),
    Lp.coeFn_smul (2/(1-c.value)) (ell:Hq),Lp.coeFn_smul (2/(1-c.value)^2) Cq,
    Lp.coeFn_smul (2*c.value*(q:ℂ)^(1-c.value)/(1-c.value)^2) (SingularCounting.powerL2 (barC c)),
    plain_read,intervalConstant_coeFn q,SingularCounting.power_coeFn (barC c),
    ae_restrict_mem (measurableSet_symmetricInterval q),ae_restrict_of_ae (volume.ae_ne (0:ℝ))]
    with x left added subtracted scaled constantScaled powerScaled logarithm constant power inside nonzero
  rw [left,added,Pi.add_apply,subtracted,Pi.sub_apply,scaled,constantScaled,powerScaled,
    Pi.smul_apply,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,smul_eq_mul,
    logarithm,constant,mul_one,power]
  unfold quarterRaw SingularCounting.powerRaw
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  have positive:0 < |x|:=abs_pos.mpr nonzero
  have small:|x|≤q:=abs_le.mpr inside
  rw [plain_integral c |x| positive small]
  have powers:((|x|:ℝ):ℂ)^(c.value-1)*((|x|:ℝ):ℂ)^(1-c.value)=1:=by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),
      show (c.value-1)+(1-c.value)=0 by ring,Complex.cpow_zero]
  have realLog:plainRaw |x|=plainRaw x:=by simp only [plainRaw,Real.log_abs]
  unfold primitive
  rw [plainRaw,sub_self,zero_add]
  rw [realLog]
  field_simp [denominator c]
  linear_combination powers*(plainRaw x*(1-c.value)-1)

/-- The genuine plain-log source is an eigen-column plus its complete fractional source contact. -/
theorem actual_plain_log_step (c:BurnolCompletedMellinCoordinate):
    centeredQuarterStep (barC c) ell=
      (2/(1-c.value)) • ell+
      (2*c.value*(q:ℂ)^(1-c.value)/(1-c.value)^2) • SingularCounting.centeredPower (barC c):=by
  have full:=congrArg Constructor.zeroMean (plain_quarter c)
  rw [map_add,map_sub,map_smul,map_smul,map_smul,Constructor.zeroMean_constant,smul_zero,sub_zero] at full
  have centered:Constructor.zeroMean (ell:Hq)=ell:=Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ell
  rw [centered] at full
  exact full

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.PlainLog
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
