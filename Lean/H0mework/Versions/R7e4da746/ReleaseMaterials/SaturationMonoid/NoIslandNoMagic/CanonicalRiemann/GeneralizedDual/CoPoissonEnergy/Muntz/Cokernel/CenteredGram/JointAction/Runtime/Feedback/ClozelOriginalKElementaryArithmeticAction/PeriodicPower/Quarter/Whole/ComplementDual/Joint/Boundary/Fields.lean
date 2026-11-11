import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fixed

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Realizer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.WholeResidual OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CountedXi OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open OriginalKPairedBEulerJunctionSource
open scoped Topology InnerProductSpace
local notation "P"=>burnolEvenAmbientProjection
local notation "F"=>fourierL2
local notation "R"=>burnolDirectRightResolventCLM
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "K"=>burnolCompletedMellinRieszVector
local notation "Q"=>pairedBurnolMultiplicativeDilation (Real.log stageZeroSonineQ)
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "BI"=>burnolMeanZeroBlockInverse
local notation "Rq"=>burnolQuarterRestriction
local notation "P0"=>Constructor.zeroMean
local instance physicalComplete:CompleteSpace BurnolPaAmbientCarrier:=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def wholeArm (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):BurnolL2:=
  ((R (barC c))^(order c.value)) (F (wholeValue c zero h positive))

def compactMass (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):ℂ:=
  burnolQuarterMeanCoefficient (compactCorrection c zero)

def originalUnit:BurnolPaAmbientCarrier:=P ConstantDual.seed

private theorem floor_even (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    reflectL2 (fullFloorValue c zero)=fullFloorValue c zero:=
  burnolReflectL2_eq_of_even_raw _ _ (actual_full_floor_raw c zero) (actual_floor_even c.value c.belowOne)

private theorem direct_split (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    directValue c zero h positive (order c.value)=wholeArm c zero h positive+powerValue c zero:=by
  rw [directValue,jointValue,map_add,fourierL2_fourierL2,floor_even c zero,map_add]
  rfl

/-- The original K is matched in the whole physical carrier, with the actual residual and complete Unit kept. -/
theorem actual_original_K_match (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    rieszAmplitude c • K c=
      P (wholeResidual c zero h positive (order c.value-1))+enrichedPa c (order c.value-1)-
        P (wholeArm c zero h positive)-compactMass c zero • originalUnit:=by
  have orderPositive:=generatedRiemannXiZeroOrder_pos (burnolPaZeroObservation c zero)
    (burnolPaZeroObservation_nontrivial c zero)
  change 0<order c.value at orderPositive
  have full:=congrArg P (direct_split c zero h positive)
  rw [map_add,actual_power_physical_source] at full
  have fixed:P (enrichedPa c (order c.value-1):BurnolL2)=enrichedPa c (order c.value-1):=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  have residual:P (wholeResidual c zero h positive (order c.value-1))=
      P (directValue c zero h positive (order c.value))-enrichedPa c (order c.value-1):=by
    rw [wholeResidual,Nat.sub_add_cancel orderPositive,map_sub,fixed]
  change rieszAmplitude c • K c=P (wholeResidual c zero h positive (order c.value-1))+
    enrichedPa c (order c.value-1)-P (wholeArm c zero h positive)-
      burnolQuarterMeanCoefficient (compactCorrection c zero) • P ConstantDual.seed
  rw [residual,full]
  module

/-- Its normalization is generated by the original same-owner Xi leading coefficient. -/
theorem actual_K_amplitude_nonzero (c:BurnolCompletedMellinCoordinate):rieszAmplitude c≠0:=by
  have paid:=actual_count_leading_nonzero c
  have bare:generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner (star c.value) (star c.value)≠0:=by
    intro vanished
    apply paid
    rw [vanished,zero_div]
  change (-(2:ℂ)^(order c.value))*generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner (star c.value) (star c.value)≠0
  exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num:(2:ℂ)≠0))) bare

/-- The original fixed action is performed on all four actual whole fields before either B projection. -/
theorem actual_paired_K_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    rieszAmplitude c • sourceAction c=
      Q (P (wholeResidual c zero h positive (order c.value-1)):BurnolL2)+
      Q (enrichedPa c (order c.value-1):BurnolL2)-
      Q (P (wholeArm c zero h positive):BurnolL2)-
      compactMass c zero • Q (originalUnit:BurnolL2):=by
  have full:=congrArg (fun p:BurnolPaAmbientCarrier=>Q (p:BurnolL2))
    (actual_original_K_match c zero h positive)
  simpa only [Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,map_add,map_sub,map_smul,sourceAction,junctionShift] using full

def positionDrive:BurnolL2 →L[ℂ] M:=Constructor.zeroMean.comp Rq
def fourierDrive:BurnolL2 →L[ℂ] M:=
  positionDrive.comp fourierL2.toContinuousLinearEquiv.toContinuousLinearMap
def firstDrive:BurnolL2 →L[ℂ] M:=positionDrive-burnolMeanZeroTruncatedFourier.comp fourierDrive
def firstSolution:BurnolL2 →L[ℂ] M:=burnolMeanZeroBlockInverse.comp firstDrive
def secondSolution:BurnolL2 →L[ℂ] M:=fourierDrive-burnolMeanZeroTruncatedFourier.comp firstSolution
def solution (i:Fin 2):BurnolL2 →L[ℂ] M:=![firstSolution,secondSolution] i

private theorem action_even (c:BurnolCompletedMellinCoordinate):
    burnolAmbientEvenPart (sourceAction c)=sourceAction c:=by
  have parity:reflectL2 (sourceAction c)=sourceAction c:=by
    change reflectL2 ((1/2:ℂ) • (burnolMultiplicativeDilation junctionShift (K c:BurnolL2)+
      burnolMultiplicativeDilation (-junctionShift) (K c:BurnolL2)))=
      (1/2:ℂ) • (burnolMultiplicativeDilation junctionShift (K c:BurnolL2)+
      burnolMultiplicativeDilation (-junctionShift) (K c:BurnolL2))
    rw [map_smul,map_add,reflectL2_burnolMultiplicativeDilation,reflectL2_burnolMultiplicativeDilation,
      mem_evenL2ClosedFace_iff.mp (K c).property.2]
  rw [burnolAmbientEvenPart,parity]
  module

private theorem first_drive_actual (c:BurnolCompletedMellinCoordinate):
    firstDrive (sourceAction c)=sourceDrive c 0-S (sourceDrive c 1):=by
  simp only [sourceDrive,Matrix.cons_val_zero,Matrix.cons_val_one,positionDrive,fourierDrive,firstDrive,
    sub_apply,ContinuousLinearMap.comp_apply]
  unfold burnolAmbientMeanZeroPosition burnolAmbientMeanZeroFourier
  rw [action_even]
  rfl

private theorem correction_actual (c:BurnolCompletedMellinCoordinate) (i:Fin 2):
    solution i (sourceAction c)=sourceCorrection c i:=by
  fin_cases i
  · change firstSolution (sourceAction c)=sourceFirst c
    rw [firstSolution,ContinuousLinearMap.comp_apply,first_drive_actual]
    exact (source_B_inverse c).symm
  · change fourierDrive (sourceAction c)-S (firstSolution (sourceAction c))=sourceSecond c
    have first:firstSolution (sourceAction c)=sourceFirst c:=by
      rw [firstSolution,ContinuousLinearMap.comp_apply,first_drive_actual]
      exact (source_B_inverse c).symm
    have second:fourierDrive (sourceAction c)=sourceDrive c 1:=by
      change P0 (Rq (F (sourceAction c)))=burnolAmbientMeanZeroFourier (sourceAction c)
      unfold burnolAmbientMeanZeroFourier
      rw [action_even]
      rfl
    rw [first,second]
    exact (eq_sub_of_add_eq' (source_B_second c)).symm

/-- The canonical Schur input itself is generated from the four actual moved fields, with no replacement B input. -/
theorem actual_first_B_feed (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    rieszAmplitude c • (sourceDrive c 0-S (sourceDrive c 1))=
      firstDrive (Q (P (wholeResidual c zero h positive (order c.value-1)):BurnolL2))+
      firstDrive (Q (enrichedPa c (order c.value-1):BurnolL2))-
      firstDrive (Q (P (wholeArm c zero h positive):BurnolL2))-
      compactMass c zero • firstDrive (Q (originalUnit:BurnolL2)):=by
  have generated:=congrArg firstDrive (actual_paired_K_source c zero h positive)
  simpa only [map_smul,map_add,map_sub,first_drive_actual] using generated

/-- Both actual inverse fibres of the original fixed K action are delivered by those same four source fields. -/
theorem actual_B_correction_feeds (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (i:Fin 2):
    rieszAmplitude c • sourceCorrection c i=
      solution i (Q (P (wholeResidual c zero h positive (order c.value-1)):BurnolL2))+
      solution i (Q (enrichedPa c (order c.value-1):BurnolL2))-
      solution i (Q (P (wholeArm c zero h positive):BurnolL2))-
      compactMass c zero • solution i (Q (originalUnit:BurnolL2)):=by
  have generated:=congrArg (solution i) (actual_paired_K_source c zero h positive)
  simpa only [map_smul,map_add,map_sub,correction_actual] using generated

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
