import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceN1MaterialContact

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalN1MaterialWard
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



open FullQuantum
open scoped Matrix.Norms.L2Operator

local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace




open PreparationVacuumPhysicalGaussMaterialContact PreparationVacuumActionDecomposition




local instance : FiniteDimensional ℂ FullMatrix := Matrix.finiteDimensional

def sourceNativeContactFiber (p : PhysicalMomentum) (x : SourceCoordinateSlice) : FockFiber→L[ℂ] FockFiber :=
  quantizer (nativeRaw (Fin.castAdd 6 (2:Fin 3)) 1 0 p (sourceState x))

theorem sourceNativeContactFiber_smooth (p : PhysicalMomentum) (x : physicalChart) :
    ContDiffAt ℝ ∞ (sourceNativeContactFiber p) x.val :=
  (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp x.val
    ((nativeRaw_smooth _ _ _ p _ (sourceState_valid x)).comp x.val sourceState_smooth.contDiffAt)

def sourceNativeContactCore (p : PhysicalMomentum) : QuantumEnd :=
  localMultiplier (sourceNativeContactFiber p) (sourceNativeContactFiber_smooth p)

theorem sourceActualN1MaterialContact_core (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceNativeContactCore p (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=
      (-Complex.I) • weightCore
        (actualCore p (chargeAction (colorGenerator 2) (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))-
          chargeAction (colorGenerator 2) (actualCore p (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))) := by
  apply DFunLike.ext
  intro x
  by_cases inside : x∈physicalChart
  · exact sourceActualN1MaterialContact_point q p state z t nonreal ⟨x,inside⟩
  · have zero : sourceTestApprox q.F (sourceActualN1Primal q p state z t) x=0 :=
      image_eq_zero_of_notMem_tsupport (fun h=>inside ((sourceTestApprox q.F (sourceActualN1Primal q p state z t)).tsupport_subset h))
    change sourceNativeContactFiber p x (sourceTestApprox q.F (sourceActualN1Primal q p state z t) x)=
      (-Complex.I) • weightFiber x (actualFiber p x (sourceColorChargeFiber (sourceTestApprox q.F (sourceActualN1Primal q p state z t) x))-
        sourceColorChargeFiber (actualFiber p x (sourceTestApprox q.F (sourceActualN1Primal q p state z t) x)))
    simp only [zero,map_zero,sub_zero,smul_zero]

private theorem comm_add (A B : QuantumEnd) :
    sourceColorWardOperator (A+B)=sourceColorWardOperator A+sourceColorWardOperator B := by
  apply LinearMap.ext
  intro f
  simp only [sourceColorWardOperator,LinearMap.comp_apply,LinearMap.add_apply,LinearMap.sub_apply,map_add]
  abel
private theorem comm_sub (A B : QuantumEnd) :
    sourceColorWardOperator (A-B)=sourceColorWardOperator A-sourceColorWardOperator B := by
  apply LinearMap.ext
  intro f
  simp only [sourceColorWardOperator,LinearMap.comp_apply,LinearMap.sub_apply,map_sub]
  abel

theorem sourceActualCoreWard_generated (p : PhysicalMomentum) :
    sourceColorWardOperator (actualCore p)=sourceColorWardOperator (fullSourceAction p)-
      sourceColorWardOperator GaussNativeForm.nativeAction+sourceColorWardOperator retainedCore := by
  have actual : fullSourceAction p=GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore p-retainedCore :=
    physical_action_decomposition p
  have coframe : sourceColorWardOperator GaussCoframeForm.coframeAction=0 := by
    apply LinearMap.ext
    intro f
    exact sub_eq_zero.mpr (LinearMap.congr_fun sourceColor_coframeAction.symm.eq f)
  rw [actual,comm_sub,comm_add,comm_add,coframe,add_zero]
  abel

theorem sourceActualN1MaterialContact_gauss (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceNativeContactCore p (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=
      (-Complex.I) • weightCore
        (sourceColorWardOperator (fullSourceAction p) (sourceTestApprox q.F (sourceActualN1Primal q p state z t))-
          sourceColorWardOperator GaussNativeForm.nativeAction (sourceTestApprox q.F (sourceActualN1Primal q p state z t))+
          sourceColorWardOperator retainedCore (sourceTestApprox q.F (sourceActualN1Primal q p state z t))) := by
  rw [sourceActualN1MaterialContact_core q p state z t nonreal]
  change (-Complex.I) • weightCore (sourceColorWardOperator (actualCore p) _)=_
  rw [sourceActualCoreWard_generated]
  rfl

end LowEnergy.PreparationVacuumPhysicalN1MaterialWard
