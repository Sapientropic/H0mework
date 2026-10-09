import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceInternalPoleWardReturn
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceSignedCurrentPoleReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalInternalChargePoleReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open FullQuantum FullSpace CanonicalGradedSpatialSource
open PreparationPhysicalSignedCurrentPoleObserver PreparationPhysicalRemainderWardPoleReturn
open PreparationPhysicalElectromagneticDirectionReturn PreparationPhysicalNormalizedFullField
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNativePhotonScatteringSheetReturn
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalFeedback
open PreparationVacuumCausalPoleResponse PreparationVacuumMixedFieldReturn
open PreparationPhysicalVoltageEnergyIdentity PreparationPhysicalEnergyCurrentWardReturn
open PreparationPhysicalChargedEnergyVariation PreparationPhysicalChargedEnergyPoleReturn
open PreparationVacuumPhysicalFeedback PreparationPhysicalChargedVertexDomainReturn
open Filter MeasureTheory
open scoped BigOperators Matrix Topology

/-- The emitter is the computed signed-volume current with its actual opposite-mode source endpoint. -/
def sourceInternalSignedEmitter (branch : Fin 2) (q : PhysicalResponsePoint)
    (sideL edgeL sideR edgeR : Fin 2) (T epsilon s : ℝ) (n : PhysicalMomentum) : ℂ :=
  sourcePhotonLeftReader branch epsilon s n
    (sourceSignedPoleWindow q sideL edgeL sideR edgeR T epsilon n 0
      (causalLambda 0 (sourceFrequency epsilon s)))

def sourceInternalSignedField (q : PhysicalResponsePoint)
    (sideL edgeL sideR edgeR : Fin 2) (T epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  sourceWholePhotonFrequencyResidue epsilon s n*ᵥ
    sourceSignedPoleWindow q sideL edgeL sideR edgeR T epsilon n 0
      (causalLambda 0 (sourceFrequency epsilon s))

theorem sourceInternalSignedField_generated (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀q : PhysicalResponsePoint,∀sideL edgeL sideR edgeR : Fin 2,∀T : ℝ,
      sourceInternalSignedField q sideL edgeL sideR edgeR T e.val (sourceSheet branch n unit e.val) n=
        sourceInternalSignedEmitter branch q sideL edgeL sideR edgeR T e.val
          (sourceSheet branch n unit e.val) n •
            sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  intro q sideL edgeL sideR edgeR T
  rw [sourceInternalSignedField,sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor]
  exact smul_comm _ _ _

/-- The Gauss emitter supplies the original full field; the physical-space reader consumes that field without a carrier identification. -/
theorem sourceSignedEmitter_internalPhaseWard (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (q : PhysicalResponsePoint) (sL eL sR eR sideL edgeL sideR edgeR : Fin 2) (T : ℝ) :
    ∀ᶠ e in scaleApproach,
      (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyReader (sourcePhotonEnergyShift e.val n)
        sideL edgeL sideR edgeR
        (sourceInternalSignedField q sL eL sR eR T e.val (sourceSheet branch n unit e.val) n)=
        sourceInternalSignedEmitter branch q sL eL sR eR T e.val (sourceSheet branch n unit e.val) n*
          (sourceDirectionPoleCoefficient branch e.val (sourceSheet branch n unit e.val) n 0*
            sourceInternalPhaseFormFactor (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR+
          (ActionNormalization.phaseMomentum:ℂ)*
            ((sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)*
              sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n 2-
              sourceDirectionPoleCoefficient branch e.val (sourceSheet branch n unit e.val) n 0/2)*
            sourceChargedVoltageOverlap (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR-
          sourceDirectionPoleCoefficient branch e.val (sourceSheet branch n unit e.val) n 0*
            sourceInternalSpinFormFactor (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR-
          ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*
            sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n 2*
            (∫k : Position,sourceEnergyRetainedWardIntegrand (sourcePhotonEnergyShift e.val n)
              sideL edgeL sideR edgeR k)+
          (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
            (sourcePoleOtherField branch e.val (sourceSheet branch n unit e.val) n)
            (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR) := by
  filter_upwards [sourceInternalSignedField_generated branch n unit] with e factor
  rw [factor,map_smul,smul_eq_mul]
  have generated:=sourcePoleEnergy_internalPhaseWard branch e.val (sourceSheet branch n unit e.val) n
    e.property.1.ne' sideL edgeL sideR edgeR
  linear_combination sourceInternalSignedEmitter branch q sL eL sR eR T e.val
    (sourceSheet branch n unit e.val) n*generated

end LowEnergy.PreparationPhysicalInternalChargePoleReturn
