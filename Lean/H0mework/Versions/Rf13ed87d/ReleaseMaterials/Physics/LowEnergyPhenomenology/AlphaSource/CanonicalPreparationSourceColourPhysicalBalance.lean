import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativeJointMode

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalNativeColourReturn
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
open CanonicalPhysicalSpatial






open PreparationVacuumPhysicalN1MaterialWard

def sourceColourContactRemainderCore (pL pR : PhysicalMomentum) (f : QuantumTest) : QuantumTest :=
  weightActionTorque pL (chargeAction (colorGenerator 2) f)+
    weightCore (CanonicalPhysicalWardCore.currentAction (pL-pR) (colorGenerator 2) f)+
    weightCore (sourceColorWardOperator GaussNativeForm.nativeAction f)-
    weightCore (sourceColorWardOperator retainedCore f)

def sourceColourContactRemainderReturn (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (y : H) : H :=
  sourceApprox q.F (embed (sourceColourContactRemainderCore pL pR (sourceTestApprox q.F y)))+
    leftCompressionDefect pL q.F (weightCore (chargeAction (colorGenerator 2) (sourceTestApprox q.F y)))+
    leftUncutDefect pL q.F (weightCore (chargeAction (colorGenerator 2) (sourceTestApprox q.F y)))-
    sourceApprox q.F (embed (weightCore (chargeAction (colorGenerator 2)
      (rightCompressionDefect pR q.F y+rightUncutDefect pR q.F y))))

theorem sourceColourContactReturn_split (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (y : H) :
    sourceColourContactWardReturn q pL pR y=
      Complex.I • sourceApprox q.F (embed (sourceNativeContactCore pR (sourceTestApprox q.F y)))+
        sourceColourContactRemainderReturn q pL pR y := by
  unfold sourceColourContactWardReturn sourceColourContactWardCore
    sourceColourContactRemainderReturn sourceColourContactRemainderCore
  simp only [map_add,map_sub,map_smul]
  abel_nf

def sourceColourContactRemainderRead (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) : ℂ :=
  ((sourcePoleDual q.epsilon q.precision pL left).comp
    (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0))
      (sourceColourContactRemainderReturn q pL pR (sourceActualN1Primal q pR right q.w t))

private theorem time_balance {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : M→ₗ[ℂ] ℂ) (n r : M) :
    -Complex.I*L (Complex.I • n+r)=L n-Complex.I*L r := by
  rw [map_add,map_smul]
  simp only [smul_eq_mul]
  have scalar : -Complex.I*Complex.I=1 := by simp
  calc
    _=(-Complex.I*Complex.I)*L n-Complex.I*L r := by ring
    _=L n-Complex.I*L r := by rw [scalar,one_mul]

theorem sourceActualColourContactRead_split (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) :
    sourceActualColourContactWardRead q pL pR left right t=
      sourceNativeJointRead q pL pR left right t-Complex.I*sourceColourContactRemainderRead q pL pR left right t := by
  unfold sourceActualColourContactWardRead sourceColourContactRemainderRead
  rw [sourceColourContactReturn_split,sourceNativeJointRead_contactCore]
  exact time_balance ((sourcePoleDual q.epsilon q.precision pL left).comp
    (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0)).toLinearMap _ _

theorem sourceConstraintChargeFirst_completeContact (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceConstraintChargeFirst q pL pR left right t=
      sourceNativeJointRead q pL pR left right t-Complex.I*sourceColourContactRemainderRead q pL pR left right t := by
  rw [sourceConstraintChargeFirst_actualWard q pL pR left right t nonrealL nonrealR,
    sourceActualColorWardRead_N1 q pL pR left right t nonrealR,
    sourceActualColourContactWard_read q pL pR left right t nonrealR,
    sourceActualColourContactRead_split]

theorem sourceActualMode_completeGauss (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    (gaugeScale/2 : ℝ) • (sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 1 0)-
      sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 2 1))=
      sourceConstraintChargeFirst q pL pR left right t+
        Complex.I*sourceColourContactRemainderRead q pL pR left right t-
        sourceDeviationJointRead q pL pR left right t := by
  rw [sourceActualMode_fullJoint,sourceConstraintChargeFirst_completeContact q pL pR left right t nonrealL nonrealR]
  ring

theorem sourceActualModeWindow_completeGauss (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    (gaugeScale/2 : ℝ) • (sourcePoleCurrentWindow q pL pR left right lambda T (gaugeSlot 1 0)-
      sourcePoleCurrentWindow q pL pR left right lambda T (gaugeSlot 2 1))=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t*(sourceConstraintChargeFirst q pL pR left right t+
        Complex.I*sourceColourContactRemainderRead q pL pR left right t-
        sourceDeviationJointRead q pL pR left right t) := by
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  have i1:IntervalIntegrable (fun t=>laplaceWeight lambda t*sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 1 0)) volume 0 T :=
    (weight.mul (sourcePoleActionEuler_continuous q pL pR left right (gaugeSlot 1 0))).intervalIntegrable 0 T
  have i2:IntervalIntegrable (fun t=>laplaceWeight lambda t*sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 2 1)) volume 0 T :=
    (weight.mul (sourcePoleActionEuler_continuous q pL pR left right (gaugeSlot 2 1))).intervalIntegrable 0 T
  unfold sourcePoleCurrentWindow
  rw [←intervalIntegral.integral_sub i1 i2,←intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t _
  change (gaugeScale/2 : ℝ) •
    (laplaceWeight lambda t*sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 1 0)-
      laplaceWeight lambda t*sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 2 1))=
    laplaceWeight lambda t*(sourceConstraintChargeFirst q pL pR left right t+
      Complex.I*sourceColourContactRemainderRead q pL pR left right t-sourceDeviationJointRead q pL pR left right t)
  rw [←sourceActualMode_completeGauss q pL pR left right t nonrealL nonrealR]
  simp only [Complex.real_smul]
  ring

theorem sourceActualCosource114_completeGauss (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceActualCurrentCosource q pL pR left right spatial lambda T 114=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*(sourceNativeJointRead q pL pR left right t-
        Complex.I*sourceColourContactRemainderRead q pL pR left right t))+
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceConstraintCovariant q pL pR left right spatial t)-
        (laplaceWeight lambda T*sourceConstraintCharge q pL pR left right T-
          sourceConstraintCharge q pL pR left right 0) := by
  rw [sourceActualCosource114_ColourContactWard q pL pR left right spatial lambda T nonrealL nonrealR]
  simp_rw [sourceActualColourContactRead_split]

end LowEnergy.PreparationVacuumPhysicalNativeColourReturn
