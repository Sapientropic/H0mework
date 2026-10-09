import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCoulombWard
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceVoltageHamiltonianResponse
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceGaussActionTimeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMPoleWard

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedVoltagePhase
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential CanonicalGradedSpatialSource
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open GaussCoreHilbert PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open GaussNativeMatter CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization GaussComposite.PhysicalEMPoleWard
open PreparationVacuumActionFieldLift GaussComposite.PhysicalEMGaugeRealization
open PreparationPhysicalActionUnits GaussComposite.PhysicalEMVoltage PreparationPhysicalNormalizedFullField GaussComposite.ActualDressedSourcePreparation GaussComposite.ActualDressedSourceResponse PreparationVacuumFullElectricWard

open ActualDressedActionPhase ActualDressedFullCoulomb ActualDressedCoulombWard
open PreparationPhysicalVoltageNoether PreparationVacuumStaticVoltageSource
open PreparationVacuumSourcePreparedResponse PreparationVacuumFieldConstraintResponse CanonicalPhysicalYResolvent
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull sourceDressedResponse

/-- The complete original voltage variation retains its scalar Cauchy slope before any charge read. -/
theorem original_voltage_time_weight (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates)
    (value slope : ℝ) (electric : Fin 3→ℝ) :
    rawActionSymbol (sourceVoltageCoordinates value slope electric) p s=
      -(sourceTimeWeight s*SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s)) := by
  rw [rawActionSymbol_source _ p s valid,sourceVoltageField_direction,sourceVoltageSymbol_first p s valid]
  rw [sourceTimeWeight_original]
  simp only [smul_mul_assoc]
  module

/-- The same original phase normalizer acts on the whole voltage and scalar coefficient, never on the Green. -/
theorem canonical_voltage_time_return (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates)
    (value slope : ℝ) (electric : Fin 3→ℝ) :
    canonicalPhaseNormalizer s*((Stage10.ActionNormalization.actionScale:ℂ) •
      rawActionSymbol (sourceVoltageCoordinates value slope electric) p s)=
        -SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s) := by
  rw [original_voltage_time_weight p s valid,smul_neg,mul_neg,←smul_mul_assoc,←mul_assoc,
    canonical_phase_time_weight s valid,one_mul]

private theorem branches_add (A B : SourceMatrix) :
    SourceRealScalarFock.branches (A+B)=SourceRealScalarFock.branches A+SourceRealScalarFock.branches B := by
  ext i j
  cases i <;> cases j <;> simp [SourceRealScalarFock.branches,Matrix.map_apply,Matrix.fromBlocks,Matrix.add_apply,add_comm]

private theorem branches_smul (r : ℝ) (A : SourceMatrix) :
    SourceRealScalarFock.branches (r • A)=r • SourceRealScalarFock.branches A := by
  ext i j
  cases i <;> cases j <;> simp [SourceRealScalarFock.branches,Matrix.map_apply,Matrix.fromBlocks,Matrix.smul_apply,Complex.real_smul]

private theorem branches_nativeY :
    SourceRealScalarFock.branches ((-Complex.I) • GaussNativeMatter.nativePrimal nativeY)=
      -chargeMatrix nativeY := by
  unfold chargeMatrix GaussNativeMatter.nativeFull SourceRealScalarFock.branches
  ext i j
  cases i <;> cases j <;> simp [Matrix.map_apply,Matrix.fromBlocks,Matrix.smul_apply]

/-- The full independent-dual current has its source-generated Y part and actual scalar Hamiltonian remainder. -/
theorem canonical_voltage_joint_return (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates)
    (value slope : ℝ) (electric : Fin 3→ℝ) :
    canonicalPhaseNormalizer s*((Stage10.ActionNormalization.actionScale:ℂ) •
      rawActionSymbol (sourceVoltageCoordinates value slope electric) p s)=
        value • chargeMatrix nativeY-slope • SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s) := by
  rw [canonical_voltage_time_return p s valid,sourceVoltageHamiltonian_split s valid.2,
    branches_add,branches_smul,branches_smul,branches_nativeY,neg_add,smul_neg,neg_neg,sub_eq_add_neg]

/-- The original full CAR normal-order pair is retained on the created N2 sector. -/
theorem canonical_voltage_quantized_return (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates)
    (value slope : ℝ) (electric : Fin 3→ℝ) :
    quantized (value • chargeMatrix nativeY-slope • SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s))=
      quantized (canonicalPhaseNormalizer s)*
        quantized ((Stage10.ActionNormalization.actionScale:ℂ) •
          rawActionSymbol (sourceVoltageCoordinates value slope electric) p s)-
      pairFiber (canonicalPhaseNormalizer s) ((Stage10.ActionNormalization.actionScale:ℂ) •
        rawActionSymbol (sourceVoltageCoordinates value slope electric) p s) := by
  have paid:=quantized_normal_order (canonicalPhaseNormalizer s)
    ((Stage10.ActionNormalization.actionScale:ℂ) •rawActionSymbol (sourceVoltageCoordinates value slope electric) p s)
  rw [canonical_voltage_joint_return p s valid] at paid
  exact eq_sub_of_add_eq paid.symm

/-- The actual response test consumes the original time-normalized Y/scalar quantum current on the same source chart. -/
theorem dressed_voltage_phase_return (event : DressedEvent) (value slope : ℝ) (electric : Fin 3→ℝ)
    (x : physicalChart) :
    quantized (value • chargeMatrix nativeY-slope • SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian (sourceState x.val)))
        (sourceTestApprox event.frame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy) x.val)=
      quantized (canonicalPhaseNormalizer (sourceState x.val))
        (quantized ((Stage10.ActionNormalization.actionScale:ℂ) •
          rawActionSymbol (sourceVoltageCoordinates value slope electric) event.momentum (sourceState x.val))
          (sourceTestApprox event.frame
            (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy) x.val))-
      pairFiber (canonicalPhaseNormalizer (sourceState x.val))
        ((Stage10.ActionNormalization.actionScale:ℂ) •
          rawActionSymbol (sourceVoltageCoordinates value slope electric) event.momentum (sourceState x.val))
        (sourceTestApprox event.frame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy) x.val) := by
  exact congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (sourceTestApprox event.frame
    (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy) x.val))
    (canonical_voltage_quantized_return event.momentum (sourceState x.val) (sourceState_valid x) value slope electric)

end LowEnergy.GaussComposite.ActualDressedVoltagePhase
