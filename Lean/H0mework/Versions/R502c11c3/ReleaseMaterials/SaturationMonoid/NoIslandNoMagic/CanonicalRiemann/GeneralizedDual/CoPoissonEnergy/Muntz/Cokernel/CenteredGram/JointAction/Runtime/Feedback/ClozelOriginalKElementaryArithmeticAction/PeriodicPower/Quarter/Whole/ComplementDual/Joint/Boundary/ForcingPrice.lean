import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.ActedPrice
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.ForcingPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKCoefficientBFiniteAction OriginalKElementaryArithmeticAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FourField
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace
open private outgoing_even from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.ActedSchur
open private evenPart_left from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog
local notation "R"=>burnolDirectRightResolventCLM
local notation "q"=>(1/4:ℝ)
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "Cq"=>intervalConstant q
local notation "mu"=>burnolQuarterMeanCoefficient
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "h₀"=>Real.log stageZeroSonineQ

private theorem gap_coefficient_mean (v:BurnolL2):
    burnolAmbientGapCoefficient q v=mu (burnolQuarterRestriction v):=by
  simp only [burnolAmbientGapCoefficient,burnolQuarterMeanCoefficient,smul_apply,
    ContinuousLinearMap.comp_apply,innerSL_apply_apply,smul_eq_mul,Complex.ofReal_pow]
  change ((‖Cq‖:ℂ)^2)⁻¹*inner ℂ Cq (burnolQuarterRestriction v)=
    inner ℂ Cq (burnolQuarterRestriction v)/(‖Cq‖:ℂ)^2
  ring

private theorem elementary_amplitude (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (j:ℕ):
    nativeActedAmplitude c j= -2*inner ℂ (elementarySource c) (nativeOutgoingCotest c j):=by
  have read:=burnolAmbientCompletedMellinRieszVector_readback c (nativeOutgoingCotest c j)
  rw [burnolAmbientCompletedMellinRieszVector_eq_kernelFormula] at read
  have original:inner ℂ (elementarySource c) (nativeOutgoingCotest c j)=
      burnolAmbientCompletedMellinEvaluator c (nativeOutgoingCotest c j):=by
    rw [elementarySource,evenPart_left _ _ (outgoing_even c zero j),read]
  rw [original,nativeActedAmplitude]
  simp only [burnolAmbientCompletedMellinEvaluator,burnolRadiusAmbientCompletedMellinEvaluator,
    burnolUnscaledCommonGapRadius,add_apply,smul_apply,smul_eq_mul,gap_coefficient_mean]
  change -2*(sourceTail (barC c) (nativeOutgoingCotest c j)+
    mu (nativeActedQuarter c j)*(q:ℂ)^(1-star (barC c).value)/(1-star (barC c).value))=
    -2*((q:ℂ)^(1-c.value)/(1-c.value)*mu (burnolQuarterRestriction (nativeOutgoingCotest c j))+
      burnolRadiusMellinTailEvaluator q _ c.value c.rightHalf (nativeOutgoingCotest c j))
  simp only [sourceTail,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,nativeActedQuarter]
  ring

/-- The full whole-forcing leg is its same-source outgoing amplitude, retaining tail and quarter mean. -/
theorem actual_native_forcing_amplitude_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (j:ℕ):
    inner ℂ (((R c)^j) (nativeCotest c)) (ForcingWhole.whole c)=
      -(star (nativeActedAmplitude c j))/2:=by
  have moved:=fourierL2.inner_map_map (fourierL2.symm (((R c)^j) (nativeCotest c))) (elementarySource c)
  rw [fourierL2.apply_symm_apply,actual_native_acted_field c zero j] at moved
  change inner ℂ (((R c)^j) (nativeCotest c)) (ForcingWhole.whole c)=_ at moved
  rw [moved]
  calc
    _=star (inner ℂ (elementarySource c) (nativeOutgoingCotest c j)):=(inner_conj_symm _ _).symm
    _=_:=by
      rw [elementary_amplitude c zero j]
      simp only [star_mul,star_neg,star_ofNat]
      ring

/-- Both native legs now have actual source prices; the complete original Unit remains explicit. -/
theorem actual_original_acted_native_bill (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field.rieszAmplitude c*OriginalRieszFinitePairing.evaluatorSource c h₀=
      (1/2:ℂ)*star (nativeActedAmplitude c (order c.value))+
      inner ℂ (burnolAmbientMeanZeroFourier (nativeOutgoingCotest c (order c.value)))
        (ForcingPrimitive.leadingCoefficient c • OriginalKFiniteOrderRelease.UnitPowerJordanSource.logBFirst c 0-
          burnolRieszSingleFourierSource c)-
      star (∫x:ℝ,star (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source.seedRaw c.value x)*
        burnolMeanZeroFourierRaw (burnolAmbientMeanZeroSecondCorrection
          (nativeOutgoingCotest c (order c.value))) x ∂μq)-
      compactMass c zero*fixedFee c (originalUnit:BurnolL2):=by
  have actual:=actual_native_boundary_bill c zero
  rw [actual_native_source,inner_add_right,inner_neg_right,
    actual_native_forcing_amplitude_price c zero,actual_native_acted_correction_price c zero] at actual
  rw [actual]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.ForcingPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
