import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceInternalChargeFormFactor

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalInternalChargePoleReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open FullQuantum FullSpace CanonicalGradedSpatialSource
open PreparationPhysicalNativePhaseChargeInventory PreparationPhysicalRemainderWardPoleReturn
open PreparationPhysicalElectromagneticDirectionReturn PreparationPhysicalNormalizedFullField
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNativePhotonScatteringSheetReturn
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalVoltageEnergyIdentity
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalFilteredChargeVoltage
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationPhysicalChargedEnergyVariation PreparationPhysicalChargedEnergyPoleReturn
open PreparationVacuumPhysicalFeedback PreparationPhysicalChargedVertexDomainReturn
open Filter MeasureTheory
open scoped BigOperators Matrix InnerProductSpace Topology

/-- The same original phase-current operator is consumed at the actual physical momentum transfer. -/
theorem sourceInternalPhaseFormFactor_original (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceInternalPhaseFormFactor shift sideL edgeL sideR edgeR=
      sourceChargedQuantumRead sideL edgeL sideR edgeR
        (sourcePhaseCurrentOperator.comp (PacketNoise.phaseShift shift).toContinuousLinearMap) := by
  simp only [sourceInternalPhaseFormFactor,sourcePhaseCurrentOperator,
    sourceChargedQuantumRead_generated,ContinuousLinearMap.comp_apply,
    smul_apply,inner_smul_right]
  rfl

/-- The whole physical pole now exposes its actual internal charge, spin action, original input/damping Ward and complete other field. -/
theorem sourcePoleEnergy_internalPhaseWard (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyReader (sourcePhotonEnergyShift epsilon n)
      sideL edgeL sideR edgeR (sourceNativeFrequencyPolarization branch epsilon s n)=
      sourceDirectionPoleCoefficient branch epsilon s n 0*
        sourceInternalPhaseFormFactor (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*
        ((sourceFrequency epsilon s:ℂ)*sourcePoleCoordinates branch epsilon s n 2-
          sourceDirectionPoleCoefficient branch epsilon s n 0/2)*
        sourceChargedVoltageOverlap (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR-
      sourceDirectionPoleCoefficient branch epsilon s n 0*
        sourceInternalSpinFormFactor (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR-
      ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*sourcePoleCoordinates branch epsilon s n 2*
        (∫k : Position,sourceEnergyRetainedWardIntegrand (sourcePhotonEnergyShift epsilon n)
          sideL edgeL sideR edgeR k)+
      (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
        (sourcePoleOtherField branch epsilon s n) (sourcePhotonEnergyShift epsilon n)
          sideL edgeL sideR edgeR := by
  rw [sourcePoleEnergy_twoCurrents branch epsilon s n nonzero,
    sourceLockedFormFactor_internalPhase,sourceFilteredChargeFormFactor_generated]
  ring

/-- Every term uses the same source physical-frequency residue and its independently generated emitter. -/
theorem sourcePoleResidue_internalPhaseWard (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (sideL edgeL sideR edgeR : Fin 2) :
    ∀ᶠ e in scaleApproach,∀leg : SourcePhotonLeg,
      (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyReader (sourcePhotonEnergyShift e.val n)
        sideL edgeL sideR edgeR (sourcePhotonFrequencyResidue leg e.val (sourceSheet branch n unit e.val) n)=
        sourcePhotonEmitter leg branch e.val (sourceSheet branch n unit e.val) n*
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
  filter_upwards [sourcePhotonFrequencyResidue_fluxFactor branch n unit] with e factor
  intro leg
  rw [factor leg,map_smul,smul_eq_mul]
  have generated:=sourcePoleEnergy_internalPhaseWard branch e.val (sourceSheet branch n unit e.val) n
    e.property.1.ne' sideL edgeL sideR edgeR
  linear_combination sourcePhotonEmitter leg branch e.val (sourceSheet branch n unit e.val) n*generated

end LowEnergy.PreparationPhysicalInternalChargePoleReturn
