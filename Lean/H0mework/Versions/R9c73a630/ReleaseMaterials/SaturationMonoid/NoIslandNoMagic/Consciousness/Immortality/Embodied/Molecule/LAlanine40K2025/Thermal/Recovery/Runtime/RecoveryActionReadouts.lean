import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Runtime.RecoveryActionWorld

/-! # Phase-exact control and thermodynamic accounts of the remembered PCE current -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Runtime

open Propagation.Producer Powered.Dynamics Load.Source Load.Producer Load.Recovery.Control
open Load.Producer.RecoveryLedger Recovery.Producer

noncomputable section

structure RecoveryControlRead where
  hamiltonian : LoadedJoint
  action : Matrix.unitaryGroup (PairController × Fin 2) ℂ
  duration : ℚ
  switchInWork : ℝ
  switchOutWork : ℝ

def recoveryControlRead : RecoveryCurrent → RecoveryControlRead
  | .ingress =>
    { hamiltonian := bareHamiltonian recoveryHamiltonian 2
      action := Load.Quantum.localUnitary (minimalPCUnitary (3 * (nativeClockStep : ℝ)))
        (environmentUnitary (3 * (nativeClockStep : ℝ)))
      duration := 3 * nativeClockStep
      switchInWork := controlSwitchInWork recoveryHamiltonian recoveryReceivedState
      switchOutWork := controlSwitchOutWork recoveryHamiltonian recoveryStateFirst }
  | .running _ =>
    { hamiltonian := loadTotalHamiltonian
      action := loadUnitary (nativeClockStep : ℝ)
      duration := nativeClockStep
      switchInWork := 0
      switchOutWork := 0 }

def recoveryEventWork : RecoveryCurrent → ℝ
  | .ingress => recoveryWork recoveryReceivedState
  | .running _ => 0

/-- The existing reachability proof will certify that the ingress work is paid once. -/
def recoveryAccumulatedWork : RecoveryCurrent → ℝ
  | .ingress => 0
  | .running _ => recoveryWork recoveryReceivedState

theorem recoveryControl_work (current : RecoveryCurrent) :
    (recoveryControlRead current).switchInWork + (recoveryControlRead current).switchOutWork =
      recoveryEventWork current := by
  cases current with
  | ingress => rfl
  | running _ => exact add_zero 0

theorem recoveryControl_duration_positive (current : RecoveryCurrent) :
    0 < (recoveryControlRead current).duration := by
  cases current with
  | ingress => exact mul_pos (by norm_num) nativeClockStep_positive
  | running _ => exact nativeClockStep_positive

theorem recoveryNext_joint (current : RecoveryCurrent) :
    (recoveryCurrentState (recoveryNext current)).joint =
      Thermal.Quantum.conjugation (recoveryControlRead current).action
        (recoveryCurrentState current).joint := by
  cases current with
  | ingress => exact recoveryStep_joint recoveryReceivedState
  | running state => exact loadStateNext_joint state

theorem recoveryNext_clock (current : RecoveryCurrent) :
    (recoveryCurrentState (recoveryNext current)).localClock =
      (recoveryCurrentState current).localClock + (recoveryControlRead current).duration := by
  cases current <;> rfl

theorem recoveryNext_energyBalance (current : RecoveryCurrent) :
    (pcEnergy (recoveryCurrentState (recoveryNext current)).joint - pcEnergy (recoveryCurrentState current).joint) +
      (environmentEnergy (recoveryCurrentState (recoveryNext current)).joint -
        environmentEnergy (recoveryCurrentState current).joint) +
      (boundaryEnergy (recoveryCurrentState (recoveryNext current)).joint -
        boundaryEnergy (recoveryCurrentState current).joint) = recoveryEventWork current := by
  cases current with
  | ingress => exact recoveryStep_fullEnergyBalance recoveryReceivedState
  | running state => exact loadStateNext_energyBalance state

theorem recoveryNext_workBalance (current : RecoveryCurrent) :
    totalEnergy (recoveryCurrentState (recoveryNext current)) - totalEnergy (recoveryCurrentState current) =
      recoveryEventWork current := by
  have balance := recoveryNext_energyBalance current
  simp only [totalEnergy, totalEnergy_split]
  linarith

theorem recoveryNext_netAccount (current : RecoveryCurrent) :
    (loadBindingAccountedFreeEnergy (recoveryCurrentState (recoveryNext current)) -
      loadBindingAccountedFreeEnergy (recoveryCurrentState current)) +
      (loadEntropyProduction (recoveryCurrentState (recoveryNext current)) -
        loadEntropyProduction (recoveryCurrentState current)) = recoveryEventWork current := by
  cases current with
  | ingress => exact recoveryStep_netAccount recoveryReceivedState
  | running state =>
    change (loadBindingAccountedFreeEnergy (loadStateNext state) - loadBindingAccountedFreeEnergy state) +
      (loadEntropyProduction (loadStateNext state) - loadEntropyProduction state) = 0
    linarith [loadStateNext_freeEnergyBalance state]

theorem recoveryAccumulatedWork_next (current : RecoveryCurrent) :
    recoveryAccumulatedWork (recoveryNext current) =
      recoveryAccumulatedWork current + recoveryEventWork current := by
  cases current with
  | ingress => exact (zero_add _).symm
  | running _ => exact (add_zero _).symm

structure RecoveryEnergyRead where
  pcInclusive : ℝ
  environment : ℝ
  boundary : ℝ
  pair : ℝ
  recipient : ℝ
  pcInteraction : ℝ
  total : ℝ

def recoveryEnergyRead (state : LoadState) : RecoveryEnergyRead :=
  ⟨pcEnergy state.joint, environmentEnergy state.joint, boundaryEnergy state.joint,
    pairEnergy state, recipientEnergy state, pcInteractionEnergy state, totalEnergy state⟩

structure RecoveryCapacityRead where
  pair : ℝ
  recipient : ℝ
  pcInclusive : ℝ
  pairPassive : ℝ
  recipientPassive : ℝ

def recoveryCapacityRead (state : LoadState) : RecoveryCapacityRead :=
  ⟨Powered.Producer.poweredPairCapacity (pcRead state),
    Powered.Producer.poweredControllerCapacity (pcRead state),
    Powered.Producer.poweredJointCapacity (pcRead state),
    Powered.Producer.poweredPairPassiveEnergy (pcRead state),
    Powered.Producer.poweredControllerPassiveEnergy (pcRead state)⟩

end

end LAlanine40K2025.Thermal.Recovery.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
