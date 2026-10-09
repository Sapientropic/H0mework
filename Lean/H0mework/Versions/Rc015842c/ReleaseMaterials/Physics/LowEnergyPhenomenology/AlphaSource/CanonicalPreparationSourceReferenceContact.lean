import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceN1NormalWard
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceModeGaugeAction
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPrimitiveColorFields

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalModeContact
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

open PreparationVacuumOriginalGreenFeedback

open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology

open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _

open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion

open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherForm sourceApprox sourceTestApprox

open PreparationVacuumPhysicalColorWard
local instance : NormedAlgebra ℚ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] sourcePolePrepared sourceExcitedProjection

open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation

def sourceReferenceState : ActionState := configurationState Stage9C.Material.SpinPair.actual 0

def sourceModeField : Field289 := gaugeField 1 0-gaugeField 2 1

private theorem color2_bracket (j : Fin 3) :
    p286CoordinateLieBracket (colorGenerator 2) (colorGenerator j)=
      ![-colorGenerator 1,colorGenerator 0,0] j := by
  change jointP286CoordinateLieBracket _ _=_
  rw [colorGenerator_bracket]
  fin_cases j <;> rfl

private theorem referenceGauge (mu : Fin 4) :
    (show NativeLie from p286CoordinateEquiv (Stage9C.Material.SpinPair.actual.gaugeConnection 0 mu))=
      Fin.cases 0 (fun j=>gaugeScale • colorGenerator j) mu := by
  refine Fin.cases ?_ (fun j=>?_) mu
  · change p286CoordinateEquiv 0=0
    exact map_zero _
  · change gaugeCoordinates SourceQuantumResidualGaugeSlice.sourceGauge j=gaugeScale • colorGenerator j
    exact sourceGauge_apply j

private theorem drop_spin {B : Type*} [Ring B] (G S A : B) (commute : G*S=S*G) :
    G*(S+A)-(S+A)*G=G*A-A*G := by
  rw [mul_add,add_mul,commute]
  noncomm_ring

private theorem referenceConnection (mu : Fin 4) :
    nativePrimal (colorGenerator 2)*(sourceReferenceState.2.1 mu)-
      sourceReferenceState.2.1 mu*nativePrimal (colorGenerator 2)=
      -(gaugeScale/2 : ℝ) • (if mu=1 then nativePrimal (originalUnit 0) else 0)-
        (-(gaugeScale/2 : ℝ) • (if mu=2 then nativePrimal (originalUnit 1) else 0)) := by
  dsimp only [sourceReferenceState,configurationState]
  rw [originalConnection_source,drop_spin _ _ _ (originalSpin_internal_commute _ _),←originalGauge_commutator,referenceGauge]
  cases mu using Fin.cases with
  | zero =>
    simp only [Fin.cases_zero,show p286CoordinateLieBracket (colorGenerator 2) 0=0 from
      (p286CoordinateLieBracketBilinear (colorGenerator 2)).map_zero,map_zero,
      if_neg (by decide : (0:Fin 4)≠1),if_neg (by decide : (0:Fin 4)≠2),smul_zero,sub_self]
  | succ j =>
    simp only [Fin.cases_succ]
    rw [p286CoordinateLieBracket_smul_right,color2_bracket,map_smul]
    fin_cases j
    · rw [sourceRawZero_color,map_smul]
      norm_num [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,map_neg,smul_smul,Fin.ext_iff]
    · rw [sourceRawOne_color,map_smul]
      norm_num [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,smul_smul,neg_smul,Fin.ext_iff]
    · norm_num [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,map_zero,Fin.ext_iff]

theorem sourceReferenceContact_generated :
    stateContact (Fin.castAdd 6 (2:Fin 3)) 1 sourceReferenceState=
      -(gaugeScale/2 : ℝ) • fieldDirection sourceModeField := by
  have direction : fieldDirection sourceModeField=fieldDirection (gaugeField 1 0)-fieldDirection (gaugeField 2 1) :=
    (fieldDirectionLinear.map_sub _ _)
  rw [direction,gauge_direction,gauge_direction]
  have frame : nativeFrameGenerator (Fin.castAdd 6 (2:Fin 3))=0:=rfl
  have generator : nativeMatterGenerator (Fin.castAdd 6 (2:Fin 3))=nativePrimal (colorGenerator 2):=rfl
  apply Prod.ext
  · simp only [stateContact,frame,Prod.smul_fst,Prod.fst_sub,smul_zero,zero_mul,sub_self]
  apply Prod.ext
  · funext mu
    change _=-(gaugeScale/2 : ℝ) • ((if mu=1 then nativePrimal (originalUnit 0) else 0)-
      (if mu=2 then nativePrimal (originalUnit 1) else 0))
    rw [smul_sub]
    simpa only [stateContact,nativeMatterGenerator,Fin.addCases_left,one_smul,colorGenerator] using referenceConnection mu
  · have vacancy:=scalarDirection_vacuum (2:Fin 3) 1
    have scalar : Stage9C.Material.SpinPair.actual.scalar 0=SourceQuantumScalarChart.vacuum := by rw [actual_scalar];rfl
    dsimp only [stateContact,sourceReferenceState,configurationState]
    rw [generator,one_smul]
    simp only [Prod.smul_snd,Prod.snd_sub,sub_self,smul_zero]
    change (nativePrimal (colorGenerator 2)*scalarLinear (Stage9C.Material.SpinPair.actual.scalar 0)-
      scalarLinear (Stage9C.Material.SpinPair.actual.scalar 0)*nativePrimal (colorGenerator 2))=0
    rw [scalar,←originalScalar_commutator]
    have zero : SourceQuantumScalarChart.action SourceQuantumScalarChart.vacuum (colorGenerator 2)=0 := by
      simpa only [PreparationVacuumNativeFieldInjection.scalarDirection,one_smul,colorLie,colorGenerator] using vacancy
    rw [zero,map_zero]

def sourceModeDeviation (z : SourceCoordinateSlice) : ActionState :=
  stateContact (Fin.castAdd 6 (2:Fin 3)) 1 (sourceState z-sourceReferenceState)

theorem sourceEmittedContact_generated (z : SourceCoordinateSlice) :
    stateContact (Fin.castAdd 6 (2:Fin 3)) 1 (sourceState z)=
      -(gaugeScale/2 : ℝ) • fieldDirection sourceModeField+sourceModeDeviation z := by
  have split : sourceState z=sourceReferenceState+(sourceState z-sourceReferenceState) := by abel
  have h:=congrArg (contactLinear (Fin.castAdd 6 (2:Fin 3)) 1) split
  rw [map_add] at h
  exact h.trans (congrArg (fun v : ActionState=>v+sourceModeDeviation z) sourceReferenceContact_generated)

end LowEnergy.PreparationVacuumPhysicalModeContact
