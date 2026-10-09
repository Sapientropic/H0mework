import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceReferenceContact

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

open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation

def sourceNativeContactSymbol (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FullMatrix :=
  nativeRaw (Fin.castAdd 6 (2:Fin 3)) 1 0 p (sourceState z)

def sourceModeDeviationSymbol (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FullMatrix :=
  -(4:ℂ) • (sourceActionWeight (sourceState z)*symbolFirst p (sourceState z) (sourceModeDeviation z))

private theorem raw_direction_sum {E A : Type*} [AddCommGroup E] [Module ℝ E]
    [Ring A] [Algebra ℂ A]
    (D : E→ₗ[ℝ] A) (W : A) (c : ℝ) (X Y : E) :
    -(4:ℂ) • (W * D (c • X + Y))=
      c • (-(4:ℂ) • (W*D X))+(-(4:ℂ) • (W*D Y)) := by
  rw [D.map_add,D.map_smul,mul_add,mul_smul_comm,smul_add,smul_comm (-(4:ℂ)) c]

private theorem modeSymbol_direction (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    -(4:ℂ) • (sourceActionWeight s*symbolFirst p s (fieldDirection sourceModeField))=sourceModeSymbol s := by
  have direction : fieldDirection sourceModeField=fieldDirection (gaugeField 1 0)-fieldDirection (gaugeField 2 1) :=
    fieldDirectionLinear.map_sub _ _
  unfold symbolFirst
  rw [direction,map_sub,mul_sub,smul_sub]
  change -(4:ℂ) • (sourceActionWeight s*symbolFirst p s (fieldDirection (gaugeField 1 0)))-
    (-(4:ℂ) • (sourceActionWeight s*symbolFirst p s (fieldDirection (gaugeField 2 1))))=sourceModeSymbol s
  rw [←rawActionSymbol_source (gaugeField 1 0) p s valid,←rawActionSymbol_source (gaugeField 2 1) p s valid]
  exact sourceModeSymbol_generated p s valid.1

/-- The mode is the original reference colour contact, with the actual emitted configuration contact retained. -/
theorem sourceNativeContactSymbol_generated (p : PhysicalMomentum) (z : physicalChart) :
    sourceNativeContactSymbol p z.val=
      -(gaugeScale/2 : ℝ) • sourceModeSymbol (sourceState z.val)+sourceModeDeviationSymbol p z.val := by
  have actual : stateVariation (Fin.castAdd 6 (2:Fin 3)) 1 0 (sourceState z.val)=
      stateContact (Fin.castAdd 6 (2:Fin 3)) 1 (sourceState z.val) := by
    simp only [stateVariation,stateContact,Pi.zero_apply,zero_smul,sub_zero]
  unfold sourceNativeContactSymbol nativeRaw nativeFirst
  rw [actual,sourceEmittedContact_generated]
  have h:=raw_direction_sum ((fderiv ℝ (sourceSymbol p) (sourceState z.val)).toLinearMap)
    (sourceActionWeight (sourceState z.val)) (-(gaugeScale/2 : ℝ)) (fieldDirection sourceModeField) (sourceModeDeviation z.val)
  change _=-(gaugeScale/2 : ℝ) • sourceModeSymbol (sourceState z.val)+
    (-(4:ℂ) • (sourceActionWeight (sourceState z.val)*symbolFirst p (sourceState z.val) (sourceModeDeviation z.val)))
  exact h.trans (congrArg (fun v : FullMatrix=>-(gaugeScale/2 : ℝ) • v+sourceModeDeviationSymbol p z.val)
    (modeSymbol_direction p (sourceState z.val) (sourceState_valid z)))

end LowEnergy.PreparationVacuumPhysicalModeContact
