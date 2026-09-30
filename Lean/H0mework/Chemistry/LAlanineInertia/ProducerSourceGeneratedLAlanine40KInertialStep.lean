import H0mework.Chemistry.LAlanineInertia.ProducerSourceGeneratedInertialKinematics
import H0mework.Chemistry.LAlanineInertia.ProducerSourceGeneratedInertialForceEnergy
import H0mework.Chemistry.LAlanineInertia.ProducerSourceGeneratedInertialKineticReadout
import H0mework.Chemistry.LAlanineInertia.ProducerSourceGeneratedInertialResolution

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Producer

open Mechanics
open LAlanine40K2025.Inertia.Source

def firstStepClosure : Prop :=
  stepReadout.currentLedger = Force.Source.updateReadout.targetEnergyLedger ∧
  stepReadout.currentPositionPicobohr = Force.Source.updateReadout.recordedTargetPositions ∧
  stepReadout.currentNuclei = Force.Source.updateReadout.targetNuclei ∧
  stepReadout.targetNuclei = stepReadout.currentNuclei ∧
  stepReadout.targetNuclei.size = 13 ∧
  (∀ atom, 0 < stepReadout.masses atom) ∧
  stepReadout.duration = Propagation.Producer.nativeClockStep ∧
  stepReadout.current.momentum = 0 ∧
  stepReadout.target.phase = addResidual referenceNext explicitResidual ∧
  (∀ atom axis, |stepReadout.positionResidual atom axis| < (2 : ℚ) / 10 ^ 15) ∧
  (∀ atom axis, |stepReadout.momentumResidual atom axis| < (2 : ℚ) / 10 ^ 20) ∧
  stepReadout.target.position ≠ stepReadout.current.position ∧
  stepReadout.target.momentum ≠ stepReadout.current.momentum ∧
  stepReadout.currentGradientComponents.size = 6 ∧
  stepReadout.targetGradientComponents.size = 6 ∧
  (∀ atom axis, forceComponentSum stepReadout.currentGradientComponents atom axis +
    stepReadout.currentGradientRoundingResidual atom axis = stepReadout.currentGradientPicohartree atom axis) ∧
  (∀ atom axis, forceComponentSum stepReadout.targetGradientComponents atom axis +
    stepReadout.targetGradientRoundingResidual atom axis = stepReadout.targetGradientPicohartree atom axis) ∧
  stepReadout.currentLedger.rowToIntegralExact ∧
  stepReadout.targetLedger.rowToIntegralExact ∧
  (stepReadout.targetLedger.grandRowSum + stepReadout.targetLedger.rowResidualSum +
    stepReadout.targetLedger.componentRoundingResidual + stepReadout.targetLedger.scfRecomputationResidual =
      stepReadout.targetLedger.reportedSCF) ∧
  0 < stepReadout.target.kinetic ∧
  |nativeKineticResidual| < (1 : ℚ) / 10 ^ 24 ∧
  stepReadout.target.potential ≠ stepReadout.current.potential ∧
  fineEnergyArithmeticResidual = (186993141223 : ℚ) / 38685626227668133590597632 ∧
  schemeAndSCFResidual = (-57361597785575 : ℚ) / 38685626227668133590597632 ∧
  (stepReadout.target.total = momentumKinetic + stepReadout.target.potential +
    nativeKineticResidual + fineEnergyArithmeticResidual) ∧
  (stepReadout.target.total - stepReadout.current.total = schemeAndSCFResidual + fineEnergyArithmeticResidual) ∧
  verletStep stepReadout.masses (-stepReadout.duration) stepReadout.target.force stepReadout.current.force
    stepReadout.target.phase = addResidual stepReadout.current.phase
      (reverseResidual stepReadout.masses stepReadout.duration explicitResidual) ∧
  (∀ atom axis, |stepReadout.current.force atom axis + (stepReadout.currentGradientPicohartree atom axis : ℚ) / 10 ^ 12| <
    (1 : ℚ) / (2 * 10 ^ 12)) ∧
  (∀ atom axis, |stepReadout.target.force atom axis + (stepReadout.targetGradientPicohartree atom axis : ℚ) / 10 ^ 12| <
    (1 : ℚ) / (2 * 10 ^ 12)) ∧
  (∀ atom axis, |stepReadout.current.position atom axis - (stepReadout.currentPositionPicobohr atom axis : ℚ) / 10 ^ 12| <
    (1 : ℚ) / (2 * 10 ^ 12)) ∧
  (∀ atom axis, |stepReadout.target.position atom axis - (stepReadout.targetPositionPicobohr atom axis : ℚ) / 10 ^ 12| <
    (1 : ℚ) / (2 * 10 ^ 12)) ∧
  |stepReadout.current.potential - (stepReadout.currentLedger.reportedSCF : ℚ) / 10 ^ 9| < (1 : ℚ) / (2 * 10 ^ 9) ∧
  |stepReadout.target.potential - (stepReadout.targetLedger.reportedSCF : ℚ) / 10 ^ 9| < (1 : ℚ) / (2 * 10 ^ 9)

/-- A fixed first inertial update, certified from raw output rather than supplied endpoints. -/
theorem sourceGeneratedFirstStep : firstStepClosure :=
  ⟨currentLedger_eq_parent, currentPositionPicobohr_eq_parent, currentNuclei_eq_parent,
    nuclei_preserved, target_nuclei_count, masses_positive, duration_eq_nativeClock,
    initial_momentum_zero, targetPhase_reconstruction, positionResidual_bound, momentumResidual_bound,
    actual_position_changed, actual_momentum_changed, current_gradient_six_components,
    target_gradient_six_components, currentGradientWholeLedger, targetGradientWholeLedger,
    currentEnergyRows_exact, targetEnergyRows_exact, targetWholeEnergyClosure, actual_kinetic_positive,
    nativeKineticResidual_bound, actual_potential_changed, fineEnergyArithmeticResidual_exact,
    schemeAndSCFResidual_exact, mechanicalEnergyWholeAccount, rawEnergyWholeAccount,
    actual_reverse_residual, currentForce_resolution, targetForce_resolution,
    currentPosition_resolution, targetPosition_resolution, currentPotential_resolution, targetPotential_resolution⟩

end LAlanine40K2025.Inertia.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
