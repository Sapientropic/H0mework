import H0mework.Chemistry.LAlanineJointNext.ProducerNuclearKinematics
import H0mework.Chemistry.LAlanineJointNext.ProducerNuclearForce
import H0mework.Chemistry.LAlanineJointNext.ProducerNuclearEnergy
import H0mework.Chemistry.LAlanineJointNext.ProducerNuclearAccount

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

noncomputable section

def nuclearClosure : Prop :=
  type_of% Source.currentFrame_eq_parent ∧
  type_of% Source.currentLedger_eq_parent ∧
  type_of% Source.masses_eq_parent ∧
  type_of% Source.duration_eq_original ∧
  type_of% nuclearCurrentNuclei_eq_parent ∧
  type_of% nuclearNuclei_preserved ∧
  type_of% nuclearNuclei_count ∧
  (∀ atom, 0 < Source.stepReadout.nuclear.masses atom) ∧
  0 < Source.stepReadout.nuclear.duration ∧
  type_of% nuclearPhase_reconstruction ∧
  type_of% nuclearPositionResidual_bound ∧
  type_of% nuclearMomentumResidual_bound ∧
  type_of% nuclearPosition_changed ∧
  type_of% nuclearMomentum_changed ∧
  type_of% nuclearInitialMomentum_not_zero ∧
  type_of% nuclearReference_reverse ∧
  type_of% nuclearActual_reverse_residual ∧
  type_of% nuclearCurrent_gradient_six ∧
  type_of% nuclearTarget_gradient_six ∧
  type_of% nuclearCurrentGradientWholeLedger ∧
  type_of% nuclearTargetGradientWholeLedger ∧
  type_of% nuclearCurrentForce_resolution ∧
  type_of% nuclearTargetForce_resolution ∧
  type_of% nuclearCurrentPosition_resolution ∧
  type_of% nuclearTargetPosition_resolution ∧
  type_of% nuclearCurrentGradientResidual_bound ∧
  type_of% nuclearTargetGradientResidual_bound ∧
  type_of% nuclearCurrentEnergyRows_exact ∧
  type_of% nuclearTargetEnergyRows_exact ∧
  type_of% nuclearCurrentWholeEnergy ∧
  type_of% nuclearTargetWholeEnergy ∧
  type_of% nuclearTargetEnergyResiduals ∧
  type_of% nuclearTargetEnergyCensus ∧
  type_of% nuclearTargetElectronBalance ∧
  type_of% nuclearTargetDoubleCounting ∧
  type_of% nuclearTargetOperator_not_energy ∧
  type_of% nuclearCurrentPotential_resolution ∧
  type_of% nuclearTargetPotential_resolution ∧
  type_of% nuclearCurrentTotal_is_sum ∧
  type_of% nuclearTargetTotal_is_sum ∧
  type_of% nuclearRecordedEnergyChange ∧
  type_of% nuclearWholeEnergyAccount ∧
  type_of% nuclearEngineVsPhysicalAccount ∧
  type_of% nuclearEngineResidual_positive_small ∧
  type_of% nuclearRecordedResidual_negative_small ∧
  type_of% nuclearKinetic_increases ∧
  type_of% nuclearPotential_decreases ∧
  type_of% nuclearTotal_decreases ∧
  type_of% nuclearEngine_not_recorded_change

theorem sourceGeneratedNuclearJointStep : nuclearClosure :=
  ⟨Source.currentFrame_eq_parent, Source.currentLedger_eq_parent, Source.masses_eq_parent, Source.duration_eq_original,
    nuclearCurrentNuclei_eq_parent, nuclearNuclei_preserved, nuclearNuclei_count,
    Inertia.Producer.masses_positive, Propagation.Producer.nativeClockStep_positive,
    nuclearPhase_reconstruction, nuclearPositionResidual_bound, nuclearMomentumResidual_bound,
    nuclearPosition_changed, nuclearMomentum_changed, nuclearInitialMomentum_not_zero,
    nuclearReference_reverse, nuclearActual_reverse_residual,
    nuclearCurrent_gradient_six, nuclearTarget_gradient_six, nuclearCurrentGradientWholeLedger, nuclearTargetGradientWholeLedger,
    nuclearCurrentForce_resolution, nuclearTargetForce_resolution, nuclearCurrentPosition_resolution, nuclearTargetPosition_resolution,
    nuclearCurrentGradientResidual_bound, nuclearTargetGradientResidual_bound,
    nuclearCurrentEnergyRows_exact, nuclearTargetEnergyRows_exact, nuclearCurrentWholeEnergy, nuclearTargetWholeEnergy,
    nuclearTargetEnergyResiduals, nuclearTargetEnergyCensus, nuclearTargetElectronBalance,
    nuclearTargetDoubleCounting, nuclearTargetOperator_not_energy, nuclearCurrentPotential_resolution, nuclearTargetPotential_resolution,
    nuclearCurrentTotal_is_sum, nuclearTargetTotal_is_sum, nuclearRecordedEnergyChange, nuclearWholeEnergyAccount,
    nuclearEngineVsPhysicalAccount, nuclearEngineResidual_positive_small, nuclearRecordedResidual_negative_small,
    nuclearKinetic_increases, nuclearPotential_decreases, nuclearTotal_decreases, nuclearEngine_not_recorded_change⟩

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
