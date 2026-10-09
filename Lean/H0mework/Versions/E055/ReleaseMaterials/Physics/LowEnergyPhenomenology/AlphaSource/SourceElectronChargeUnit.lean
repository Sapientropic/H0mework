import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualChargeTransition
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointPreparedCoupling

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalElectronChargeUnitReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalJointEMCouplingUnitReturn
open PreparationPhysicalPhaseGaugeRealization
open FullQuantum FullSpace YangMills.FullPairing
open Stage10 Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource
open PreparationPhysicalCommonCurrentStaticRead
open Electromagnetic.CanonicalCoframe
open SourceQuantumResidualGaugeSlice SourceQuantumScalarChart GaussNativeMatter
open GaussComposite
open PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalNativePhaseChargeInventory
open PreparationPhysicalChargedPacketQuantumReturn
open scoped BigOperators Matrix Topology InnerProductSpace

/-- The producer uses the original electromagnetic direction itself, with no
renaming of the hypercharge or mother trace. -/
theorem sourceElectron_actual_generator_direction :
    sourcePhaseGaugeLie =
      -SourceQuantumResidualGaugeSlice.colorGenerator 2-(1/2:ℝ) • nativeY := rfl

theorem sourceElectron_joint_native_generator :
    GaussNativeMatter.nativePrimal sourcePhaseGaugeLie=
      Quantum.operatorMatrix sourceJointGenerator :=
  sourceJoint_native

/-- The electron unit is read from the actual charged source column at edge `0`.
It is source-generated; the relative CAR increment remains a separate quantity. -/
def sourceElectronChargeUnit : ℂ := (sourceActualPhaseCharge 0 : ℂ)

theorem sourceElectronChargeUnit_generated : sourceElectronChargeUnit = 1 := by
  simp [sourceElectronChargeUnit, sourceActualPhaseCharge]

theorem sourceElectronChargeUnit_abs : ‖sourceElectronChargeUnit‖ = 1 := by
  rw [sourceElectronChargeUnit_generated]
  norm_num

/-- The actual independent Dirac-dual current carries `h` times the generated
absolute electron unit. -/
theorem sourceElectronIndependent_current (side : Fin 2) :
    actual.conjugateMatter 0
      (Stage10.CanonicalMatter.canonicalDual (PreparationVacuumElectromagneticIdentity.actualRestStatePreparation (sourceChargedRestIndex side 0))
        (sourcePhaseNoether
          (PreparationVacuumElectromagneticIdentity.actualRestStatePreparation (sourceChargedRestIndex side 0) (actual.matter 0))))=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceElectronChargeUnit := by
  simpa only [sourceElectronChargeUnit] using sourceActualIndependent_current side 0

def sourceElectronNoetherUnit (side : Fin 2) : ℂ :=
  (Stage10.ActionNormalization.phaseMomentum:ℂ)⁻¹ *
    actual.conjugateMatter 0
      (Stage10.CanonicalMatter.canonicalDual (PreparationVacuumElectromagneticIdentity.actualRestStatePreparation (sourceChargedRestIndex side 0))
        (sourcePhaseNoether
          (PreparationVacuumElectromagneticIdentity.actualRestStatePreparation (sourceChargedRestIndex side 0) (actual.matter 0))))

theorem sourceElectronNoetherUnit_generated (side : Fin 2) :
    sourceElectronNoetherUnit side = sourceElectronChargeUnit := by
  unfold sourceElectronNoetherUnit
  rw [sourceElectronIndependent_current]
  have h : (Stage10.ActionNormalization.phaseMomentum:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'
  field_simp

/-- The actual filtered source current keeps its commutator correction while
using the same absolute electron unit. -/
theorem sourceElectronFiltered_current (sideL sideR : Fin 2) :
    sourceChargedQuantumRead sideL 0 sideR 0 sourcePhaseCurrentOperator=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceElectronChargeUnit*
        inner ℂ (sourceChargedFilteredPacket sideL 0) (sourceChargedFilteredPacket sideR 0)+
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*inner ℂ (sourceChargedFilteredPacket sideL 0)
        (sourceActualChargeCorrection sideR 0) := by
  simpa only [sourceElectronChargeUnit] using sourceActualCharge_current sideL 0 sideR 0

/-- Every scalar/matter joint letter retains the fractional source character;
this is not the electron unit. -/
theorem sourceElectron_joint_fractional_character (addition : Bool) :
    sourceJointIncrement addition = if addition then (1/2:ℂ) else -(1/2:ℂ) := by
  cases addition <;> norm_num [sourceJointIncrement]

theorem sourceElectron_joint_increment_ne_unit (addition : Bool) :
    sourceJointIncrement addition ≠ sourceElectronChargeUnit := by
  rw [sourceElectronChargeUnit_generated]
  cases addition <;> norm_num [sourceJointIncrement]

/-- A simultaneous nonzero field/current rescaling leaves the normalized
Noether charge read unchanged. -/
theorem sourceElectron_rescale_invariant (side : Fin 2) (lambda : ℂ) (hlambda : lambda ≠ 0) :
    lambda⁻¹ * (lambda *
      ((Stage10.ActionNormalization.phaseMomentum:ℂ)⁻¹ *
        actual.conjugateMatter 0
          (Stage10.CanonicalMatter.canonicalDual (PreparationVacuumElectromagneticIdentity.actualRestStatePreparation (sourceChargedRestIndex side 0))
            (sourcePhaseNoether
              (PreparationVacuumElectromagneticIdentity.actualRestStatePreparation (sourceChargedRestIndex side 0) (actual.matter 0))))))=
      sourceElectronChargeUnit := by
  change lambda⁻¹ * (lambda * sourceElectronNoetherUnit side)=sourceElectronChargeUnit
  rw [sourceElectronNoetherUnit_generated]
  field_simp

end LowEnergy.PreparationPhysicalElectronChargeUnitReturn
