import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFilteredCanonicalCharge

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFilteredChargeVoltage
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open FullQuantum FullSpace Stage9C.Material.SpinPair
open PreparationVacuumNoetherChart PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumPhysicalFeedback PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumActionFieldLift PreparationVacuumMatterEulerFeedback PreparationVacuumOriginalGreenFeedback
open PreparationPhysicalVoltageEnergyIdentity PreparationPhysicalVoltageCompleteReturn
open PreparationPhysicalChargedEnergyVariation PreparationPhysicalChargedEnergyPoleReturn
open PreparationPhysicalVoltageNoetherChargeReturn PreparationPhysicalChargedPacketQuantumReturn
open MeasureTheory Filter
open scoped Topology BigOperators Matrix

/-- The test current now comes from the same filtered external packet used in the complete energy read. -/
def sourceFilteredVoltageResponse (q : PhysicalResponsePoint) (force : Field289) (shift : Position)
    (z : physicalSpectralDomain (physicalMomentum shift)) (T : ℝ) (side edge : Fin 2) : ℂ :=
  -(∫x,sourceFilteredCurrent side edge side edge x)*
    sourcePhysicalEnergyReader shift side edge side edge
      (deriv (actionFieldCurve q force (physicalMomentum shift) z T) 0)

/-- Both powers of h are actual source currents: the four-mode forcing and the filtered test packet. -/
theorem sourceFilteredVoltageResponse_generated (q : PhysicalResponsePoint) (force : Field289) (shift : Position)
    (z : physicalSpectralDomain (physicalMomentum shift)) (nonzero : z.val≠0)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) (side edge : Fin 2) :
    sourceFilteredVoltageResponse q force shift z T side edge=
      -(ActionNormalization.phaseMomentum:ℂ)^2/(2*(lapse:ℂ)*(spatialSquare (physicalMomentum shift):ℂ))*
        sourceVoltageUnitGaussSource q force true (physicalMomentum shift) z.val T*
        sourceChargedVoltageOverlap shift side edge side edge-
      (ActionNormalization.phaseMomentum:ℂ)*sourcePreparedVoltageAmplitude q force (physicalMomentum shift) z.val T*
        sourceFullEnergyRead
          (originalChange (fullMomentum (physicalSpatial (physicalMomentum shift)) z.val)*ᵥ(nullProjection*ᵥ
            (originalInverse (fullMomentum (physicalSpatial (physicalMomentum shift)) z.val)*ᵥ
              sourceVoltageLaplaceRamp (physicalSpatial (physicalMomentum shift)) z.val))) shift side edge side edge+
      (ActionNormalization.phaseMomentum:ℂ)*sourceFullEnergyRead
        (PreparationVacuumOriginalGreenFeedback.sourceField
          ⟨fullMomentum (physicalSpatial (physicalMomentum shift)) z.val,z.property⟩
          (sourcePreparedVoltageRemainder q force (physicalMomentum shift) z.val T)) shift side edge side edge := by
  rw [sourceFilteredVoltageResponse,sourceFilteredCurrent_total,neg_neg,
    sourcePreparedVoltageEnergy_gauss q force shift z nonzero hz hw T side edge side edge,
    sourceVoltageModeForcing_charge q force true (physicalMomentum shift) z.val T]
  ring

/-- Charge normalization agrees with the old maker, while both response legs here remain the filtered preparation. -/
theorem sourceFilteredVoltageResponse_quantum (q : PhysicalResponsePoint) (force : Field289) (shift : Position)
    (z : physicalSpectralDomain (physicalMomentum shift)) (T : ℝ) (side edge : Fin 2) :
    sourceFilteredVoltageResponse q force shift z T side edge=
      -sourceChargedQuantumRead side edge side edge sourceFilteredChargeOperator*
        sourcePhysicalEnergyReader shift side edge side edge
          (deriv (actionFieldCurve q force (physicalMomentum shift) z T) 0) := by
  rw [sourceFilteredCurrent_quantum]
  rfl

end LowEnergy.PreparationPhysicalFilteredChargeVoltage
