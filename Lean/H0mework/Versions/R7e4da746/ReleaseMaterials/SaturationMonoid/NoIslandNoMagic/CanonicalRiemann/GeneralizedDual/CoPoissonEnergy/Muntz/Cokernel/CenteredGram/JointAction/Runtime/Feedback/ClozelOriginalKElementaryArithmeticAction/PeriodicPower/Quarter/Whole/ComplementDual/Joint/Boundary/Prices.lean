import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FourField
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Mean

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource OriginalKPairedBEulerJunctionSource.BandFullStockEuler
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKSourceResolventReconstruction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FourField
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Mean OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mass
open scoped Topology InnerProductSpace
open private meanRead mean_read from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Mean
open private action_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields
local notation "P"=>burnolEvenAmbientProjection
local notation "F"=>fourierL2
local notation "Rq"=>burnolQuarterRestriction
local notation "E"=>burnolQuarterZeroExtension
local notation "R"=>burnolDirectRightResolventCLM
local notation "K"=>burnolCompletedMellinRieszVector
local notation "μ"=>burnolQuarterMeanCoefficient
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "h₀"=>Real.log stageZeroSonineQ
local notation "Q"=>pairedBurnolMultiplicativeDilation h₀
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "Cq"=>intervalConstant (1/4:ℝ)

/-- This actual physical covector is generated from the fixed K action and both canonical B fibres. -/
def physicalCotest (c:BurnolCompletedMellinCoordinate):BurnolPaAmbientCarrier:=
  star (pairedMellinTranslationCharacter c.value h₀) • K c-P (sourceAction c)

private theorem projection_pair (v w:BurnolL2):
    inner ℂ v (P w:BurnolL2)=inner ℂ (P v:BurnolL2) w:=by
  have left:=Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (P w) v
  have right:=Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (P v) w
  exact left.symm.trans right

private theorem paired_pair (c:BurnolCompletedMellinCoordinate) (v:BurnolL2):
    inner ℂ (K c:BurnolL2) (Q v)=inner ℂ (sourceAction c) v:=by
  have plus:inner ℂ (K c:BurnolL2) (burnolMultiplicativeDilation h₀ v)=
      inner ℂ (burnolMultiplicativeDilation (-h₀) (K c:BurnolL2)) v:=by
    have moved:=(burnolMultiplicativeDilation (-h₀)).inner_map_eq_flip (K c:BurnolL2) v
    rw [←burnolMultiplicativeDilation_neg_eq_symm,neg_neg] at moved
    exact moved.symm
  have minus:inner ℂ (K c:BurnolL2) (burnolMultiplicativeDilation (-h₀) v)=
      inner ℂ (burnolMultiplicativeDilation h₀ (K c:BurnolL2)) v:=by
    have moved:=(burnolMultiplicativeDilation h₀).inner_map_eq_flip (K c:BurnolL2) v
    rw [←burnolMultiplicativeDilation_neg_eq_symm] at moved
    exact moved.symm
  change inner ℂ (K c:BurnolL2) ((1/2:ℂ) • (burnolMultiplicativeDilation h₀ v+
    burnolMultiplicativeDilation (-h₀) v))=
    inner ℂ ((1/2:ℂ) • (burnolMultiplicativeDilation h₀ (K c:BurnolL2)+
      burnolMultiplicativeDilation (-h₀) (K c:BurnolL2))) v
  simp only [inner_smul_left,inner_smul_right,inner_add_left,inner_add_right,
    map_div₀,map_one,map_ofNat,plus,minus]
  ring

/-- Projection remains in its actual position between the whole action and the fixed boundary cotest. -/
theorem actual_projection_fee (c:BurnolCompletedMellinCoordinate) (v:BurnolL2):
    fixedFee c (P v:BurnolL2)=inner ℂ (physicalCotest c:BurnolL2) v:=by
  change inner ℂ (K c:BurnolL2)
    (pairedMellinTranslationCharacter c.value h₀ • (P v:BurnolL2)-Q (P v:BurnolL2))=_
  rw [inner_sub_right,inner_smul_right,paired_pair]
  have original:inner ℂ (K c:BurnolL2) (P v:BurnolL2)=inner ℂ (K c:BurnolL2) v:=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (K c) v
  rw [original,projection_pair (sourceAction c) v]
  simp only [physicalCotest,Submodule.coe_sub,Submodule.coe_smul,inner_sub_left,inner_smul_left,
    starRingEnd_apply,star_star]

/-- The complete two-face B correction is retained in this raw field identity. -/
theorem actual_physical_cotest_source (c:BurnolCompletedMellinCoordinate):
    (physicalCotest c:BurnolL2)=star (pairedMellinTranslationCharacter c.value h₀) • (K c:BurnolL2)-
      sourceAction c+correctionRaw c:=by
  rw [physicalCotest,Submodule.coe_sub,Submodule.coe_smul,source_action_projection]
  module

private theorem quarter_pair (v:BurnolL2):inner ℂ v ConstantDual.seed=star (μ (Rq v))/2:=by
  have read:=mean_read v
  change 2*inner ℂ Cq (Rq v)=μ (Rq v) at read
  have left:inner ℂ ConstantDual.seed v=μ (Rq v)/2:=by
    calc
      _=inner ℂ Cq (Rq v):=ContinuousLinearMap.adjoint_inner_left Rq v Cq
      _=_:=by linear_combination read/2
  calc
    _=star (inner ℂ ConstantDual.seed v):=(inner_conj_symm _ _).symm
    _=_:=by rw [left,star_div₀,star_ofNat]

private theorem first_zero (c:BurnolCompletedMellinCoordinate):
    μ (sourceFirst c:Hq)=0:=by
  have zero:inner ℂ Cq (sourceFirst c:Hq)=0:=
    (Submodule.mem_orthogonal _ _).mp (sourceFirst c).property _ (Submodule.mem_span_singleton_self _)
  simp only [burnolQuarterMeanCoefficient,zero,zero_div]

private theorem correction_mean (c:BurnolCompletedMellinCoordinate):
    μ (Rq (correctionRaw c))=μ (Rq (F (E (sourceSecond c:Hq)))):=by
  have raw:=congrArg meanRead (show correctionRaw c=E (sourceFirst c:Hq)+F (E (sourceSecond c:Hq)) from rfl)
  rw [map_add,mean_read,mean_read,mean_read,burnolQuarterRestriction_zeroExtension,first_zero,zero_add] at raw
  exact raw

/-- The fixed Unit bill is computed by the original K mean, actual moved mean and full second B return mean. -/
theorem actual_fixed_unit_fee (c:BurnolCompletedMellinCoordinate):
    fixedFee c (originalUnit:BurnolL2)=
      pairedMellinTranslationCharacter c.value h₀*(star (μ (Rq (K c:BurnolL2)))/2)-
      star (sourceMean c 0)/2+star (μ (Rq (F (E (sourceSecond c:Hq)))))/2:=by
  have source:=actual_projection_fee c ConstantDual.seed
  change fixedFee c (originalUnit:BurnolL2)=_ at source
  rw [actual_physical_cotest_source,inner_add_left,inner_sub_left,inner_smul_left,
    starRingEnd_apply,star_star,quarter_pair,quarter_pair,quarter_pair,correction_mean] at source
  have mean:μ (Rq (sourceAction c))=sourceMean c 0:=by
    unfold sourceMean sourceFace
    change μ (Rq (sourceAction c))=μ (Rq (burnolAmbientEvenPart (sourceAction c)))
    rw [action_even]
  rw [mean] at source
  exact source

/-- The whole compact mass is its original finite-part source and original Xi clock. -/
theorem actual_compact_mass_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    compactMass c zero=(2/(1-star c.value))^(order c.value)*
      (4*deriv (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation.poleFreeSource c) 1/(1-star c.value)):=by
  rw [compactMass,actual_compact_correction_mean c zero,actual_quarter_mean_finite_part c zero]

private theorem fourier_adjoint_step (c:BurnolCompletedMellinCoordinate) (v:BurnolL2):
    fourierL2.symm ((R (barC c)).adjoint v)=R c (fourierL2.symm v):=by
  rw [sourceStep_actual,sourceStep_fourier_source,fourierL2.symm_apply_apply]
  change sourceResolvent (barC c) (fourierL2.symm v)=burnolDirectRightResolvent (c.value/2) (fourierL2.symm v)
  simp only [sourceResolvent,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]

private theorem fourier_adjoint_power (c:BurnolCompletedMellinCoordinate) (j:ℕ) (v:BurnolL2):
    fourierL2.symm (((R (barC c))^j).adjoint v)=((R c)^j) (fourierL2.symm v):=by
  induction j with
  | zero=>simp only [pow_zero,ContinuousLinearMap.adjoint_one,one_apply_eq_self]
  | succ j previous=>
    change fourierL2.symm (star ((R (barC c))^(j+1)) v)=_
    rw [pow_succ,star_mul,mul_apply_eq_comp]
    change fourierL2.symm ((R (barC c)).adjoint (((R (barC c))^j).adjoint v))=_
    rw [fourier_adjoint_step,previous,pow_succ',mul_apply_eq_comp]

def wholeCotest (c:BurnolCompletedMellinCoordinate):BurnolL2:=
  ((R c)^(order c.value)) (fourierL2.symm (physicalCotest c:BurnolL2))

/-- The actual fixed-boundary whole price uses the true original-parameter R power of this generated physical cotest. -/
theorem actual_whole_boundary_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    fixedFee c (P (wholeArm c zero h positive):BurnolL2)=
      inner ℂ (wholeCotest c) (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole.wholeValue c zero h positive):=by
  rw [actual_projection_fee,wholeArm]
  rw [←ContinuousLinearMap.adjoint_inner_left]
  have fourier:=fourierL2.inner_map_map
    (fourierL2.symm (((R (barC c))^(order c.value)).adjoint (physicalCotest c:BurnolL2)))
    (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole.wholeValue c zero h positive)
  rw [fourierL2.apply_symm_apply] at fourier
  rw [fourier,fourier_adjoint_power]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
