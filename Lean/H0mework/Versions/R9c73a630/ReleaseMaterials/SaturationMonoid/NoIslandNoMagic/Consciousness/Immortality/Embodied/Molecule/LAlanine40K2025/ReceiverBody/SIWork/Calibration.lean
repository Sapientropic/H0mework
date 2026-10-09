import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.OriginalClock.Units

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
open UnifiedAction.AtomicScales
open SaturationMonoid.PhysicsCore.Stage10.ActionNormalization
noncomputable section

-- The original action's canonical energy and phase, not its frequency-mass shadow.
def sourceEnergyToJoule : ℝ := energyJoule/canonicalHartree
def sourceLengthToMeter : ℝ := lengthMeter/sourceLength
def sourceTimeToSecond : ℝ := timeSecond/sourceTime
def sourceMassToKilogram : ℝ := massKilogram/canonicalMass
def sourceActionToJouleSecond : ℝ := hbarJouleSecond/phaseMomentum

theorem source_energy_positive : 0 < sourceEnergyToJoule := div_pos energy_positive canonical_hartree_positive
theorem source_length_positive : 0 < sourceLengthToMeter := div_pos length_positive UnifiedAction.AtomicScales.length_positive
theorem source_time_positive : 0 < sourceTimeToSecond := div_pos time_positive UnifiedAction.AtomicScales.time_positive

theorem original_energy_calibrated (atomicEnergy : ℝ) :
    sourceEnergyToJoule*(canonicalHartree*atomicEnergy)=energyJoule*atomicEnergy := by
  unfold sourceEnergyToJoule
  field_simp [canonical_hartree_positive.ne']

theorem original_length_calibrated (atomicLength : ℝ) :
    sourceLengthToMeter*(sourceLength*atomicLength)=lengthMeter*atomicLength := by
  unfold sourceLengthToMeter
  field_simp [UnifiedAction.AtomicScales.length_positive.ne']

theorem original_clock_calibrated (atomicTime : ℝ) :
    sourceTimeToSecond*UnifiedAction.OriginalClock.sourceElapsed atomicTime=atomicTime*timeSecond := by
  unfold sourceTimeToSecond UnifiedAction.OriginalClock.sourceElapsed
  field_simp [UnifiedAction.AtomicScales.time_positive.ne']

theorem original_mass_calibrated : sourceMassToKilogram*canonicalMass=massKilogram :=
  div_mul_cancel₀ _ canonical_mass_positive.ne'

theorem original_action_calibrated : sourceActionToJouleSecond*phaseMomentum=hbarJouleSecond :=
  div_mul_cancel₀ _ phaseMomentum_positive.ne'

theorem calibration_action_commutes : sourceEnergyToJoule*sourceTimeToSecond=sourceActionToJouleSecond := by
  unfold sourceEnergyToJoule sourceTimeToSecond sourceActionToJouleSecond
  rw [← source_time_from_action]
  rw [timeSecond]
  field_simp [energy_positive.ne',canonical_hartree_positive.ne',phaseMomentum_positive.ne']

theorem source_mass_energy_length : canonicalHartree*canonicalMass*sourceLength^2=phaseMomentum^2 := by
  unfold canonicalHartree canonicalMass sourceLength sourceEnergy
  field_simp [UnifiedAction.AtomicScales.mass_positive.ne',UnifiedAction.coulombCoefficient_positive.ne']

theorem calibration_mass_commutes :
    sourceMassToKilogram=sourceEnergyToJoule*sourceTimeToSecond^2/sourceLengthToMeter^2 := by
  unfold sourceMassToKilogram sourceEnergyToJoule sourceTimeToSecond sourceLengthToMeter
  rw [← source_time_from_action]
  have internal := source_mass_energy_length
  unfold timeSecond energyJoule
  field_simp [mass_positive.ne',length_positive.ne',hbar_positive.ne',canonical_hartree_positive.ne',
    canonical_mass_positive.ne',phaseMomentum_positive.ne',UnifiedAction.AtomicScales.length_positive.ne']
  nlinarith only [internal]

theorem original_q_seconds : sourceTimeToSecond*UnifiedAction.OriginalClock.nativeQ=
    UnifiedAction.OriginalClock.originalQ*timeSecond := original_clock_calibrated _

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
