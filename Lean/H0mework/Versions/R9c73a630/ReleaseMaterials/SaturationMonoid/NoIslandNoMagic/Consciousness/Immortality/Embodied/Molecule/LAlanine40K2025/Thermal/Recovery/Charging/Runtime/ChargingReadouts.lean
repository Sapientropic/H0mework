import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Runtime.ChargingSourceLedger

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.Runtime

open Recovery.Runtime Powered.Dynamics Load.Source Load.Producer Load.Producer.RecoveryLedger
open Propagation.Producer Load.Recovery.Control
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Source

noncomputable section

def chargingControlRead : RecoveryCurrent → RecoveryControlRead
  | .ingress =>
    { hamiltonian := bareHamiltonian sourceHamiltonian 2
      action := Load.Quantum.localUnitary (sourceFlow (nativeClockStep : ℝ)) (environmentUnitary (nativeClockStep : ℝ))
      duration := nativeClockStep
      switchInWork := controlSwitchInWork sourceHamiltonian receivedState
      switchOutWork := controlSwitchOutWork sourceHamiltonian chargedFirst }
  | .running state => recoveryControlRead (.running state)

def chargingEventWork : RecoveryCurrent → ℝ
  | .ingress => sourceWork receivedState
  | .running _ => 0

def chargingAccumulatedWork : RecoveryCurrent → ℝ
  | .ingress => 0
  | .running _ => sourceWork receivedState

theorem chargingControl_work (current : RecoveryCurrent) :
    (chargingControlRead current).switchInWork + (chargingControlRead current).switchOutWork =
      chargingEventWork current := by
  cases current with
  | ingress => rfl
  | running state => exact recoveryControl_work (.running state)

theorem chargingControl_duration (current : RecoveryCurrent) :
    (chargingControlRead current).duration = nativeClockStep := by cases current <;> rfl

theorem chargingControl_duration_positive (current : RecoveryCurrent) :
    0 < (chargingControlRead current).duration := by
  rw [chargingControl_duration]
  exact nativeClockStep_positive

theorem chargingNext_joint (current : RecoveryCurrent) :
    (chargingCurrentState (chargingNext current)).joint =
      Quantum.conjugation (chargingControlRead current).action (chargingCurrentState current).joint := by
  cases current with
  | ingress => exact chargeStep_joint receivedState
  | running state => exact loadStateNext_joint state

theorem chargingNext_clock (current : RecoveryCurrent) :
    (chargingCurrentState (chargingNext current)).localClock =
      (chargingCurrentState current).localClock + nativeClockStep := by cases current <;> rfl

theorem chargingNext_workBalance (current : RecoveryCurrent) :
    totalEnergy (chargingCurrentState (chargingNext current)) - totalEnergy (chargingCurrentState current) =
      chargingEventWork current := by
  cases current with
  | ingress => exact (chargeStep_actual_work receivedState).symm
  | running state =>
    have balance := loadStateNext_energyBalance state
    change totalEnergy (loadStateNext state) - totalEnergy state = 0
    simp only [totalEnergy, Load.Source.totalEnergy_split]
    linarith

theorem chargingNext_energyBalance (current : RecoveryCurrent) :
    (pcEnergy (chargingCurrentState (chargingNext current)).joint - pcEnergy (chargingCurrentState current).joint) +
      (environmentEnergy (chargingCurrentState (chargingNext current)).joint -
        environmentEnergy (chargingCurrentState current).joint) +
      (boundaryEnergy (chargingCurrentState (chargingNext current)).joint -
        boundaryEnergy (chargingCurrentState current).joint) = chargingEventWork current := by
  have balance := chargingNext_workBalance current
  simp only [totalEnergy, Load.Source.totalEnergy_split] at balance
  linarith

theorem chargingNext_netAccount (current : RecoveryCurrent) :
    (loadBindingAccountedFreeEnergy (chargingCurrentState (chargingNext current)) -
      loadBindingAccountedFreeEnergy (chargingCurrentState current)) +
      (loadEntropyProduction (chargingCurrentState (chargingNext current)) -
        loadEntropyProduction (chargingCurrentState current)) = chargingEventWork current := by
  cases current with
  | ingress => exact chargeStep_netAccount receivedState
  | running state =>
    change (loadBindingAccountedFreeEnergy (loadStateNext state) - loadBindingAccountedFreeEnergy state) +
      (loadEntropyProduction (loadStateNext state) - loadEntropyProduction state) = 0
    linarith [loadStateNext_freeEnergyBalance state]

theorem chargingAccumulatedWork_next (current : RecoveryCurrent) :
    chargingAccumulatedWork (chargingNext current) = chargingAccumulatedWork current + chargingEventWork current := by
  cases current with
  | ingress => exact (zero_add _).symm
  | running _ => exact (add_zero _).symm

end
end LAlanine40K2025.Thermal.Recovery.Charging.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
