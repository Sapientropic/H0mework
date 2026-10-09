import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativeContactReader

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

def sourceNativeJointKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) : H→L[ℂ] H :=
  physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*
    PreparationVacuumNativeLocalWard.nativeReader (Fin.castAdd 6 (2:Fin 3)) 1 0 pR q.F 0*
      jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0

def sourceDeviationJointKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) : H→L[ℂ] H :=
  physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*sourceDeviationReader pR q.F*
    jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0

theorem sourceNativeJointKernel_mode (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) :
    sourceNativeJointKernel q pL pR t=
      (-(gaugeScale/2 : ℝ) : ℂ) •
        (fiveKernel (gaugeField 1 0) pR (pL-pR) q.F q.z q.w t 0-
          fiveKernel (gaugeField 2 1) pR (pL-pR) q.F q.z q.w t 0)+
      sourceDeviationJointKernel q pL pR t := by
  have momentum : pR+(pL-pR)=pL := by ext i;simp
  unfold sourceNativeJointKernel sourceDeviationJointKernel fiveKernel
  rw [sourceNativeReader_mode,momentum]
  simp only [mul_add,add_mul,mul_sub,sub_mul,smul_mul_assoc,mul_smul_comm]

def sourceNativeJointRead (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) : ℂ :=
  sourcePoleRead q.epsilon q.precision pL pR left right (sourceNativeJointKernel q pL pR t)

def sourceDeviationJointRead (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) : ℂ :=
  sourcePoleRead q.epsilon q.precision pL pR left right (sourceDeviationJointKernel q pL pR t)

private theorem mode_balance {B : Type*} [AddCommGroup B] [Module ℂ B]
    (L : B→ₗ[ℂ] ℂ) (c : ℂ) (N X Y D : B) (source : N=(-c) • (X-Y)+D) :
    c • (-L X-(-L Y))=L N-L D := by
  rw [source,map_add,map_smul,map_sub]
  simp only [smul_eq_mul]
  ring

theorem sourceActualMode_fullJoint (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) :
    (gaugeScale/2 : ℝ) • (sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 1 0)-
      sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 2 1))=
      sourceNativeJointRead q pL pR left right t-sourceDeviationJointRead q pL pR left right t := by
  rw [sourcePoleActionEuler_source,sourcePoleActionEuler_source]
  change (gaugeScale/2 : ℝ) •
    (-sourcePoleRead q.epsilon q.precision pL pR left right (fiveKernel (gaugeField 1 0) pR (pL-pR) q.F q.z q.w t 0)-
      (-sourcePoleRead q.epsilon q.precision pL pR left right (fiveKernel (gaugeField 2 1) pR (pL-pR) q.F q.z q.w t 0)))=_
  simp only [Complex.real_smul]
  exact mode_balance (sourcePoleRead q.epsilon q.precision pL pR left right).toLinearMap
    _ _ _ _ _ (by simpa only [Complex.ofReal_neg] using sourceNativeJointKernel_mode q pL pR t)

theorem sourceNativeJointRead_contactCore (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) :
    sourceNativeJointRead q pL pR left right t=
      ((sourcePoleDual q.epsilon q.precision pL left).comp
        (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0))
          (sourceApprox q.F (embed (sourceNativeContactCore pR
            (sourceTestApprox q.F (sourceActualN1Primal q pR right q.w t))))) := by
  unfold sourceNativeJointRead sourceNativeJointKernel
  rw [sourcePoleRead_actual]
  simp only [sourcePoleDual,ContinuousLinearMap.comp_apply,innerSL_apply_apply,mul_apply_eq_comp]
  rw [sourceNativeReader_contactCore]
  rfl

theorem sourceNativeJointRead_actualGauss (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (nonreal : q.w.im≠0) :
    sourceNativeJointRead q pL pR left right t=
      ((sourcePoleDual q.epsilon q.precision pL left).comp
        (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0))
          (sourceApprox q.F (embed ((-Complex.I) • weightCore
            (sourceColorWardOperator (fullSourceAction pR) (sourceTestApprox q.F (sourceActualN1Primal q pR right q.w t))-
              sourceColorWardOperator GaussNativeForm.nativeAction (sourceTestApprox q.F (sourceActualN1Primal q pR right q.w t))+
              sourceColorWardOperator retainedCore (sourceTestApprox q.F (sourceActualN1Primal q pR right q.w t)))))) := by
  rw [sourceNativeJointRead_contactCore,sourceActualN1MaterialContact_gauss q pR right q.w t nonreal]

end LowEnergy.PreparationVacuumPhysicalNativeColourReturn
