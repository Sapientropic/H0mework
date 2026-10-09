import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceConstraintBoundary

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalColorCharge
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

def sourceColorCoefficient (mu : Fin 4) (s : ActionState) : SourceMatrix :=
  densityActionMatrix*(stateVolume s • (coefficientMatrix mu s.1*nativePrimal (colorGenerator 2)))

def sourceColorSymbol (mu : Fin 4) (s : ActionState) : FullMatrix :=
  oppositeDual*SourceRealScalarFock.branches (sourceColorCoefficient mu s)

private def gaugeCoefficient (mu : Fin 4) (a : Fin 12) (s : ActionState) : SourceMatrix :=
  densityActionMatrix*(stateVolume s • (coefficientMatrix mu s.1*nativePrimal (originalUnit a)))

private theorem gaugeSymbol_generated (mu : Fin 4) (a : Fin 12) (p : PhysicalMomentum)
    (s : ActionState) (nondegenerate : s.1.det≠0) :
    rawActionSymbol (gaugeField mu a) p s=oppositeDual*SourceRealScalarFock.branches (gaugeCoefficient mu a s) := by
  unfold rawActionSymbol rawFourier
  simp only [gauge_density mu a s nondegenerate]
  change oppositeDual*realFourierMatrix
    (fun i=>densityActionMatrix*(if i=0 then stateVolume s •
      (coefficientMatrix mu s.1*nativePrimal (originalUnit a)) else 0)) p= _
  simp [realFourierMatrix,affineMatrix,gaugeCoefficient,SourceRealScalarFock.branches]

private theorem coefficient_color (mu : Fin 4) (s : ActionState) :
    (1/2 : ℝ) • (gaugeCoefficient mu 6 s-gaugeCoefficient mu 7 s)=sourceColorCoefficient mu s := by
  have source:=congrArg nativePrimal sourceConstraintDirection_color
  rw [map_smul,map_sub] at source
  unfold gaugeCoefficient sourceColorCoefficient
  rw [←source]
  simp only [mul_sub,smul_sub,mul_smul_comm]
  rw [smul_comm (1/2 : ℝ) (stateVolume s)]
  rw [smul_comm (1/2 : ℝ) (stateVolume s)]

/-- The original action weight and coframe remain inside the actual color insertion. -/
theorem sourceColorSymbol_generated (mu : Fin 4) (p : PhysicalMomentum)
    (s : ActionState) (nondegenerate : s.1.det≠0) :
    (1/2 : ℝ) • (rawActionSymbol (gaugeField mu 6) p s-
      rawActionSymbol (gaugeField mu 7) p s)=sourceColorSymbol mu s := by
  rw [gaugeSymbol_generated mu 6 p s nondegenerate,gaugeSymbol_generated mu 7 p s nondegenerate]
  unfold sourceColorSymbol
  rw [←coefficient_color mu s]
  change _=oppositeDual*branchesLinear ((1/2 : ℝ) • (gaugeCoefficient mu 6 s-gaugeCoefficient mu 7 s))
  rw [map_smul,map_sub]
  simp only [mul_sub,mul_smul_comm,smul_sub]
  rfl

def sourceColorFiber (mu : Fin 4) (z : SourceCoordinateSlice) :
    FockFiber→L[ℂ] FockFiber := quantizer (sourceColorSymbol mu (sourceState z))

theorem sourceColorFiber_generated (mu : Fin 4) (p : PhysicalMomentum) (z : physicalChart) :
    (1/2 : ℝ) • (rawStateFiber (gaugeField mu 6) p (sourceState z.val)-
      rawStateFiber (gaugeField mu 7) p (sourceState z.val))=sourceColorFiber mu z.val := by
  have h:=congrArg (quantizer.restrictScalars ℝ)
    (sourceColorSymbol_generated mu p (sourceState z.val) (coframe_nondegenerate z))
  simp only [map_smul,map_sub] at h
  exact h

end LowEnergy.PreparationVacuumPhysicalColorCharge
