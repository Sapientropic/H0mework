import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseConstraintAction
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalQuantumResidual
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPoleWard

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer
open GaussCoreHilbert CanonicalGradedSpatialSource
open CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization
open PreparationVacuumPhysicalFeedback PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSourcePreparation
open ActualDressedConstraintEndpoint ActualDressedTemporalResidual ActualDressedTemporalHalf
open ActualDressedStaticPole ActualDressedStaticResponse
open scoped Matrix

/-- All three return mouths consume the same actual created unit, source profile and physical frame in one kernel environment. -/
theorem same_event_charge_quantum_pole (event : DressedEvent) (a : Fin 12) (i j : Fin 289) :
    chargeReader sourcePhaseGaugeLie (sourceDressedUnit event.epsilon event.precision)=
      (1/2:ℂ) • sourceDressedUnit event.epsilon event.precision+actualPhaseInput event ∧
    (staticQuantumCorrection event 0 1*ᵥ(fun k=>(fieldUnit j k:ℂ))) (gaugeSlot 0 a)-
      dressedEulerObserver event (temporalGaussInitialJet (dressedKinematicPoint event 0) a (fieldUnit j))-
      Complex.I*dressedEulerObserver event (temporalPhysicalDrive (dressedKinematicPoint event 0) a (fieldUnit j) 1)-
      Complex.I*physicalPreparationMismatch event 0
        (temporalGaussHalfJet (dressedKinematicPoint event 0) a (fieldUnit j) 1)=
      Complex.I*preparationWardObserver event
        (temporalGaussHalfJet (dressedKinematicPoint event 0) a (fieldUnit j) 1) ∧
    physicalPreparationMismatch event 0
      (staticPoleLeadingOperator (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j))=
      -preparationWardObserver event
        (staticPoleLeadingOperator (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j)) := by
  exact ⟨actual_creation_phase_input event,
    temporal_quantum_preparation_return event 0 a (fieldUnit j) 1 (by norm_num),
    static_pole_preparation_return event (fieldUnit i) (fieldUnit j)⟩

theorem same_event_full_constraint (event : DressedEvent) :
    sourceHamiltonian event.momentum event.frame
      (phaseConstraintReader event.momentum event.frame (sourceDressedUnit event.epsilon event.precision))-
      phaseConstraintReader event.momentum event.frame
        (sourceHamiltonian event.momentum event.frame (sourceDressedUnit event.epsilon event.precision))=
      phaseConstraintChannels event.momentum 0 event.frame (sourceDressedUnit event.epsilon event.precision) := by
  simpa only [add_zero] using phase_constraint_hamiltonian_return event.momentum 0 event.frame
    (sourceDressedUnit event.epsilon event.precision)

end LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer

#print axioms LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_charge_quantum_pole
#print axioms LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_full_constraint
