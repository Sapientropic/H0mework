import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FourField
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFiniteSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.WholeResidual
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field
open scoped Topology InnerProductSpace
open private original_pa_price from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa
local notation "K"=>burnolCompletedMellinRieszVector
local notation "P"=>burnolEvenAmbientProjection
local notation "A"=>sourceAnnulusCut
local notation "D"=>burnolMultiplicativeDilation
local notation "h₀"=>Real.log stageZeroSonineQ
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner

def fixedBoundary (c:BurnolCompletedMellinCoordinate):BurnolL2 →L[ℂ] BurnolL2:=
  pairedMellinTranslationCharacter c.value h₀ • ContinuousLinearMap.id ℂ BurnolL2-
    pairedBurnolMultiplicativeDilation h₀

def fixedFee (c:BurnolCompletedMellinCoordinate) (value:BurnolL2):ℂ:=
  inner ℂ (K c:BurnolL2) (fixedBoundary c value)

private theorem fixed_nonnegative:0≤h₀:=Real.log_nonneg (by
  change 1≤Real.sqrt 3
  exact Real.one_le_sqrt.mpr (by norm_num))

/-- The original finite boundary field is read by its own complete self-source evaluator. -/
theorem actual_original_boundary_fee (c:BurnolCompletedMellinCoordinate):
    fixedFee c (K c:BurnolL2)=evaluatorSource c h₀:=by
  have forcing:inner ℂ (K c:BurnolL2) (forcingIntegral c h₀+forcingIntegral c (-h₀))=
      -star (sourcePairRead c h₀):=by
    calc
      _=star (inner ℂ (forcingIntegral c h₀+forcingIntegral c (-h₀)) (K c:BurnolL2)):=
        (inner_conj_symm _ _).symm
      _=_:=by rw [forcing_pair_source c h₀ fixed_nonnegative,star_neg]
  change inner ℂ (K c:BurnolL2)
    (pairedMellinTranslationCharacter c.value h₀ • (K c:BurnolL2)-sourceAction c)=_
  rw [BandFullStockAction.paired_original_source_action,inner_sub_right,inner_add_right,inner_smul_right,
    inner_smul_right,inner_smul_right,original_kernel_self_source,junctionShift,forcing]
  unfold evaluatorSource
  ring

/-- The actual generated Pa leg delivers the two moving source prices; its Unit has not been quotiented out. -/
theorem actual_pa_boundary_fee (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (j:ℕ):
    fixedFee c (enrichedPa c j:BurnolL2)=
      (-1/2:ℂ)*(inner ℂ (countedKernel c zero) (D (-h₀) (A (tateSource c (j+1))))+
        inner ℂ (countedKernel c zero) (D h₀ (A (tateSource c (j+1))))):=by
  have plus:=actual_moving_pa_price c zero j (-h₀)
  have minus:=actual_moving_pa_price c zero j h₀
  rw [neg_neg] at plus
  change inner ℂ (K c:BurnolL2)
    (pairedMellinTranslationCharacter c.value h₀ • (enrichedPa c j:BurnolL2)-
      (1/2:ℂ) • (D h₀ (enrichedPa c j:BurnolL2)+D (-h₀) (enrichedPa c j:BurnolL2)))=_
  rw [inner_sub_right,inner_smul_right,original_pa_price c zero j,mul_zero,
    inner_smul_right,inner_add_right,←plus,←minus]
  ring

/-- The complete original K boundary action is generated from the four specified actual fields. -/
theorem actual_four_field_boundary (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    rieszAmplitude c • fixedBoundary c (K c:BurnolL2)=
      fixedBoundary c (P (wholeResidual c zero h positive (order c.value-1)):BurnolL2)+
        fixedBoundary c (enrichedPa c (order c.value-1):BurnolL2)-
        fixedBoundary c (P (wholeArm c zero h positive):BurnolL2)-
        compactMass c zero • fixedBoundary c (originalUnit:BurnolL2):=by
  have generated:=congrArg (fun p:BurnolPaAmbientCarrier=>fixedBoundary c (p:BurnolL2))
    (actual_original_K_match c zero h positive)
  simpa only [Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,map_add,map_sub,map_smul] using generated

def fourFieldNet (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):ℂ:=
  fixedFee c (P (wholeResidual c zero h positive (order c.value-1)):BurnolL2)-
    fixedFee c (P (wholeArm c zero h positive):BurnolL2)-
    compactMass c zero*fixedFee c (originalUnit:BurnolL2)+
    (-1/2:ℂ)*(inner ℂ (countedKernel c zero) (D (-h₀) (A (tateSource c (order c.value))))+
      inner ℂ (countedKernel c zero) (D h₀ (A (tateSource c (order c.value)))))

/-- The original complete finite self/endpoint price is now the actual four-field source bill. -/
theorem actual_original_four_field_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    rieszAmplitude c*evaluatorSource c h₀=fourFieldNet c zero h positive:=by
  have orderPositive:=generatedRiemannXiZeroOrder_pos (burnolPaZeroObservation c zero)
    (burnolPaZeroObservation_nontrivial c zero)
  change 0<order c.value at orderPositive
  have generated:=congrArg (inner ℂ (K c:BurnolL2)) (actual_four_field_boundary c zero h positive)
  simp only [inner_smul_right,inner_sub_right,inner_add_right] at generated
  rw [←fixedFee,actual_original_boundary_fee] at generated
  change rieszAmplitude c*evaluatorSource c h₀=
    fixedFee c (P (wholeResidual c zero h positive (order c.value-1)):BurnolL2)+
      fixedFee c (enrichedPa c (order c.value-1):BurnolL2)-
      fixedFee c (P (wholeArm c zero h positive):BurnolL2)-
      compactMass c zero*fixedFee c (originalUnit:BurnolL2) at generated
  rw [actual_pa_boundary_fee c zero (order c.value-1),Nat.sub_add_cancel orderPositive] at generated
  unfold fourFieldNet
  linear_combination generated

/-- The installed original consumer uses this bill at the original order with no scalar or field replacement. -/
theorem actual_original_four_field_consumer (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    BurnolPaBoundaryCancellationAt c zero↔fourFieldNet c zero h positive=0:=by
  have original:=fixed_residual_source c zero
  have price:=actual_original_four_field_price c zero h positive
  unfold BurnolPaBoundaryCancellationAt
  rw [installedOriginalK_fixedResidual_eq_original]
  constructor
  · intro cancelled
    rw [cancelled,neg_zero] at original
    rw [←price,←original,mul_zero]
  · intro cancelled
    rw [cancelled] at price
    have evaluator:evaluatorSource c h₀=0:=(mul_eq_zero.mp price).resolve_left (actual_K_amplitude_nonzero c)
    rw [evaluator] at original
    exact neg_eq_zero.mp original

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FourField
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
