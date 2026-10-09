import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.SourceRestSpatialAction

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumRestModeCoupling
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

open Filter
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

theorem sourceRawZero_color : originalUnit 0=(2:ℝ) • colorGenerator 1:=by
  apply PreparationCoordinates.rawCoordinates.injective
  rw [map_smul]
  simp only [originalUnit,LinearEquiv.apply_symm_apply]
  change _=(2:ℝ) • PreparationCoordinates.rawRead (colorGenerator 1)
  unfold PreparationCoordinates.rawRead
  rw [colorGenerator_coordinates]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply,Fin.ext_iff]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num

theorem sourceRawOne_color : originalUnit 1=(2:ℝ) • colorGenerator 0:=by
  apply PreparationCoordinates.rawCoordinates.injective
  rw [map_smul]
  simp only [originalUnit,LinearEquiv.apply_symm_apply]
  change _=(2:ℝ) • PreparationCoordinates.rawRead (colorGenerator 0)
  unfold PreparationCoordinates.rawRead
  rw [colorGenerator_coordinates]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply,Fin.ext_iff]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num

def sourceModeCoefficient (s : ActionState) : SourceMatrix:=
  (2:ℝ) • (densityActionMatrix*(stateVolume s •
    (coefficientMatrix 1 s.1*nativePrimal (colorGenerator 1)-coefficientMatrix 2 s.1*nativePrimal (colorGenerator 0))))

def sourceModeSymbol (s : ActionState) : FullMatrix:=oppositeDual*SourceRealScalarFock.branches (sourceModeCoefficient s)

private def gaugeCoefficient (mu : Fin 4) (a : Fin 12) (s : ActionState) : SourceMatrix:=
  densityActionMatrix*(stateVolume s • (coefficientMatrix mu s.1*nativePrimal (originalUnit a)))

private theorem gaugeSymbol_generated (mu : Fin 4) (a : Fin 12) (p : PhysicalMomentum)
    (s : ActionState) (nondegenerate : s.1.det≠0) :
    rawActionSymbol (gaugeField mu a) p s=oppositeDual*SourceRealScalarFock.branches (gaugeCoefficient mu a s):=by
  unfold rawActionSymbol rawFourier
  simp only [gauge_density mu a s nondegenerate]
  change oppositeDual*realFourierMatrix
    (fun i=>densityActionMatrix*(if i=0 then stateVolume s •
      (coefficientMatrix mu s.1*nativePrimal (originalUnit a)) else 0)) p=_
  simp [realFourierMatrix,affineMatrix,gaugeCoefficient,SourceRealScalarFock.branches]

private theorem sourceModeCoefficient_generated (s : ActionState) :
    gaugeCoefficient 1 0 s-gaugeCoefficient 2 1 s=sourceModeCoefficient s:=by
  unfold gaugeCoefficient sourceModeCoefficient
  rw [sourceRawZero_color,sourceRawOne_color,map_smul,map_smul]
  simp only [mul_smul_comm,smul_sub,mul_sub]
  rw [smul_comm (stateVolume s) (2:ℝ),smul_comm (stateVolume s) (2:ℝ)]

theorem sourceModeSymbol_generated (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0) :
    rawActionSymbol (gaugeField 1 0) p s-rawActionSymbol (gaugeField 2 1) p s=sourceModeSymbol s:=by
  rw [gaugeSymbol_generated 1 0 p s nondegenerate,gaugeSymbol_generated 2 1 p s nondegenerate]
  unfold sourceModeSymbol
  rw [←sourceModeCoefficient_generated]
  change _=oppositeDual*branchesLinear (gaugeCoefficient 1 0 s-gaugeCoefficient 2 1 s)
  rw [map_sub,mul_sub]
  rfl

def sourceModeFiber (z : SourceCoordinateSlice) : FockFiber→L[ℂ] FockFiber:=quantizer (sourceModeSymbol (sourceState z))

theorem sourceModeFiber_generated (p : PhysicalMomentum) (z : physicalChart) :
    rawStateFiber (gaugeField 1 0) p (sourceState z.val)-rawStateFiber (gaugeField 2 1) p (sourceState z.val)=sourceModeFiber z.val:=by
  have h:=congrArg (quantizer.restrictScalars ℝ) (sourceModeSymbol_generated p (sourceState z.val) (coframe_nondegenerate z))
  simp only [map_sub] at h
  exact h

end LowEnergy.PreparationVacuumRestModeCoupling
