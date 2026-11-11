import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.UnitClock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.GammaBank
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.FullJet
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.Riesz OriginalKElementaryArithmeticAction.FreeParameter.UnitSplice OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossContact OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossJet
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.UnitJet OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.UnitClock
open scoped InnerProductSpace Topology BigOperators
local notation "L" => (Real.log 4:ℂ)
local notation "phase" s => fullMellinTranslationCharacter s (Real.log 16)
local notation "q" => (1/4:ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Hq" => BurnolQuarterIntervalL2
open private tate_fourier_read from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer

private theorem coefficient_analytic (base:BurnolCompletedMellinCoordinate) :
 AnalyticAt ℂ constantCoefficient base.value := by
 have nonzero:1-base.value≠0:=by
  intro same
  have realPart:=congrArg Complex.re same
  simp only [sub_re,one_re,zero_re] at realPart
  linarith [base.belowOne]
 have represented:constantCoefficient=(fun s:ℂ=>(1/2:ℂ)*(1-s)⁻¹*Complex.exp (L*s)):=
  funext OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.actual_constant_coefficient_exp
 rw [represented]
 fun_prop

/-- The original inverse is read before varying its legal source parameter. -/
theorem actual_free_unit_read (c base probe:BurnolCompletedMellinCoordinate) (h:ℝ) :
 inner ℂ (movedTest c h) (freeUnit probe.value ConstantDual.value)=
  constantCoefficient probe.value*inner ℂ (movedTest c h) ConstantDual.value-
   (1/2:ℂ)*radiusFamily base (radiusTest c h) probe.value := by
 rw [actual_free_inverse_unit,inner_sub_right,inner_smul_right,inner_smul_right,tate_fourier_read]
 change constantCoefficient probe.value*inner ℂ (movedTest c h) ConstantDual.value-
   (1/2:ℂ)*inner ℂ (unitTest c h) (burnolUnitTailResponse probe q)=_
 rw [actual_unit_radius_price,actual_radius_family_source]
 rfl

theorem actual_free_unit_jet (c base:BurnolCompletedMellinCoordinate) (h:ℝ) (m:ℕ) :
 iteratedDeriv m (fun s:ℂ=>inner ℂ (movedTest c h) (freeUnit s ConstantDual.value)) base.value=
  iteratedDeriv m constantCoefficient base.value*inner ℂ (movedTest c h) ConstantDual.value-
   (1/2:ℂ)*(phase base.value)⁻¹*
    ∑j∈Finset.range (m+1),(m.choose j:ℂ)*L^(m-j)*((j.factorial:ℂ)/(2:ℂ)^j)*
      inner ℂ (radiusTest c h) (unitJet base j) := by
 have right:{s:ℂ|(1/2:ℝ)<s.re}∈𝓝 base.value:=
  (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds base.rightHalf
 have below:{s:ℂ|s.re<1}∈𝓝 base.value:=
  (isOpen_Iio.preimage Complex.continuous_re).mem_nhds base.belowOne
 have original:(fun s:ℂ=>inner ℂ (movedTest c h) (freeUnit s ConstantDual.value))=ᶠ[𝓝 base.value]
   (fun s:ℂ=>constantCoefficient s*inner ℂ (movedTest c h) ConstantDual.value-
    (1/2:ℂ)*radiusFamily base (radiusTest c h) s):=by
  filter_upwards [right,below] with s hs ht
  exact actual_free_unit_read c base ⟨s,hs,ht⟩ h
 have first:ContDiffAt ℂ m (fun s:ℂ=>constantCoefficient s*inner ℂ (movedTest c h) ConstantDual.value)
   base.value:=(coefficient_analytic base).mul analyticAt_const |>.contDiffAt
 have second:ContDiffAt ℂ m (fun s:ℂ=>(1/2:ℂ)*radiusFamily base (radiusTest c h) s)
   base.value:=analyticAt_const.mul (radius_family_analytic base (radiusTest c h)) |>.contDiffAt
 rw [original.iteratedDeriv_eq m,iteratedDeriv_fun_sub first second,
  iteratedDeriv_mul_const_field,iteratedDeriv_const_mul_field,actual_radius_family_jet]
 ring

/-- The exact original Xi order reads the full Unit bank and the simultaneous original B contact. -/
theorem actual_complete_joint_full_jet (c base:BurnolCompletedMellinCoordinate) (h:ℝ) (m:ℕ) :
 iteratedDeriv m (completeJointModel c h) base.value=
  (1/2:ℂ)*(phase base.value)⁻¹*
    ∑j∈Finset.range (m+1),(m.choose j:ℂ)*L^(m-j)*((j.factorial:ℂ)/(2:ℂ)^j)*
      inner ℂ (radiusTest c h) (unitJet base j)-
   iteratedDeriv m constantCoefficient base.value*inner ℂ (movedTest c h) ConstantDual.value+
   jointBRead c h (iteratedDeriv m (fun s:ℂ=>(bModel s:Hq)) base.value) := by
 rw [actual_complete_joint_jet]
 have read:iteratedDeriv m (fun s:ℂ=>inner ℂ (movedTest c h) (freeUnit s ConstantDual.value)) base.value=
   inner ℂ (movedTest c h) (iteratedDeriv m (fun s:ℂ=>freeUnit s ConstantDual.value) base.value):=by
  change (iteratedFDeriv ℂ m ((innerSL ℂ (movedTest c h)) ∘ (fun s:ℂ=>freeUnit s ConstantDual.value)) base.value)
   (fun _=>1)=_
  rw [(innerSL ℂ (movedTest c h)).iteratedFDeriv_comp_left ((free_unit_analytic base ConstantDual.value).contDiffAt (n:=m)) le_rfl]
  rfl
 rw [←read,actual_free_unit_jet]
 ring

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.FullJet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
