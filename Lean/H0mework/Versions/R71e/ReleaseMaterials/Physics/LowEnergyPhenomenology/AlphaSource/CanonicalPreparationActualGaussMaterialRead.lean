import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceGaussColorWard

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalGaussMaterialContact
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
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

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


open PreparationVacuumPhysicalModeContact GaussLiveMomentum CanonicalPhysicalWardCore




open scoped ContDiff



open PreparationVacuumPhysicalGaussColorTorque

def sourceMatterTorqueSample (a b : QuantumTest) (z : SourceCoordinateSlice) : ℂ :=
  pairSample z (a z) (sourceMatterTorqueFiber z (b z))

def sourceMatterTorqueForm (a b : QuantumTest) : ℂ :=
  ∫z,sourceMatterTorqueSample a b z ∂GaussHistoryHilbert.configurationMeasure

theorem sourceMatterSample_generated (a b : QuantumTest) (z : SourceCoordinateSlice) :
    sourceMatterTorqueSample a b z=densityPair a (sourceColorWardOperator GaussMatterCore.matterAction b) z := by
  unfold sourceMatterTorqueSample
  rw [←sourceMatterTorque_generated b z,pairSample_source]

theorem sourceMatterSample_integrable (a b : QuantumTest) :
    Integrable (sourceMatterTorqueSample a b) GaussHistoryHilbert.configurationMeasure :=
  (densityPair_integrable a (sourceColorWardOperator GaussMatterCore.matterAction b)).congr
    (Eventually.of_forall (fun z=>(sourceMatterSample_generated a b z).symm))

theorem sourceMatterForm_generated (a b : QuantumTest) :
    sourceMatterTorqueForm a b=sourcePair a (sourceColorWardOperator GaussMatterCore.matterAction b) := by
  rw [sourcePair_integral]
  exact integral_congr_ae (Eventually.of_forall (sourceMatterSample_generated a b))

def sourceMatterTorqueReader (F : GaussUnitaryHistory.Index) : H→L[ℂ] H :=
  finiteRiesz F (fun i j=>sourceMatterTorqueForm (frameTest F i) (frameTest F j))

attribute [local irreducible] sourceMatterTorqueForm sourceMatterTorqueReader frameVector frameTest
  sourceColorWardOperator

theorem sourceMatterReader_return (F : GaussUnitaryHistory.Index) (y : H) :
    sourceMatterTorqueReader F y=sourceApprox F (embed
      (sourceColorWardOperator GaussMatterCore.matterAction (sourceTestApprox F y))) := by
  unfold sourceMatterTorqueReader finiteRiesz
  rw [sourceTestApprox_frame]
  simp only [map_sum,map_smul]
  simp_rw [sourceApprox_frame]
  simp only [Finset.smul_sum,sum_apply,smul_apply,InnerProductSpace.rankOne_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceMatterForm_generated]
  unfold sourcePair
  rw [frameTest_embed]
  simp only [smul_smul]
  congr 1
  ring

end LowEnergy.PreparationVacuumPhysicalGaussMaterialContact
