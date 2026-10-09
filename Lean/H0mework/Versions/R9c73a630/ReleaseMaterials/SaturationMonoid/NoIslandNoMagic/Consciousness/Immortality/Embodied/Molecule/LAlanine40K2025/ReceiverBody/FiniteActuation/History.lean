import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Integrals

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
open Thermal.Recovery.Reservoir Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
noncomputable section

theorem target_kinetic_generated :
    nuclearKinetic (fun i => (generatedBody.frame.momentum i.1 i.2 : ℝ))=(generatedBody.frame.kinetic : ℝ) := by
  change nuclearKinetic (fun i => (targetMomentumQ i : ℝ))=(nextKineticQ : ℝ)
  rw [target_kinetic]
  congr 1
  funext i
  exact (target_momentum_rational i).symm

theorem complete_historical_account :
    Live.freeEnergy generatedBody.resource.quantum+Live.entropyProduction generatedBody.resource.quantum+
      Extract.Port.kinetic generatedBody.resource.momentum+(generatedBody.frame.total : ℝ)=
    Live.entropyProduction Live.initial+Live.freeEnergy Live.initial+Live.measurementWork Live.initial+
      responseWork receivedState+responseWork received+Weak.pulseWork Weak.origin+
      Extract.pulseWork Weak.execution+responseWork Replenish.origin+
      (Reentry.Source.stepReadout.nuclear.target.total : ℝ)-(Reentry.Producer.targetKineticResidual : ℝ) := by
  rw [target_free_energy_entropy_account,input_body]
  exact ReceiverBody.full_historical_account

theorem complete_engine_account :
    (generatedBody.frame.total : ℝ)+Extract.Port.kinetic generatedBody.resource.momentum-
      ((Reentry.Source.stepReadout.nuclear.current.total : ℝ)+Extract.Port.kinetic receiverInitial)=
        (Reentry.Source.engineEnergyChange : ℝ)-(Reentry.Source.engineAccountingResidual : ℝ)-
        (Reentry.Producer.targetKineticResidual : ℝ) := by
  have current := target_mechanical_account
  rw [input_body] at current
  have original := ReceiverBody.original_engine_account
  change (targetFrame.total : ℝ)+Extract.Port.kinetic receiverTarget-
    ((Reentry.Source.stepReadout.nuclear.current.total : ℝ)+Extract.Port.kinetic receiverInitial)=_ at original
  change Extract.Port.kinetic generatedBody.resource.momentum+(generatedBody.frame.total : ℝ)=
    Extract.Port.kinetic receiverTarget+(targetFrame.total : ℝ) at current
  linarith only [current,original]

theorem target_configuration_preserved (i : Coordinate) :
    generatedBody.frame.position i.1 i.2=input.joint.body.frame.position i.1 i.2 ∧
    generatedBody.realized=input.joint.body.realized ∧
    generatedBody.held=input.joint.body.held ∧
    generatedBody.inheritedResidual=input.joint.body.inheritedResidual ∧
    generatedBody.newNumericalResidual=input.joint.body.newNumericalResidual := ⟨rfl,rfl,rfl,rfl,rfl⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
