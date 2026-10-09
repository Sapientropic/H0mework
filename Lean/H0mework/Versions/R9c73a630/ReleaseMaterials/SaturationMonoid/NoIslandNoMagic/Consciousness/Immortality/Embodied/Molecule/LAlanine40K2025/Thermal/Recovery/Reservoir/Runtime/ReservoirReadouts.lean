import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime.ReservoirLedger

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime

open Propagation.Producer
noncomputable section

structure ReservoirControlRead where
  hamiltonian : Current.FullJoint
  action : Matrix.unitaryGroup Current.FullIndex ℂ
  duration : ℚ
  switchInWork : ℝ
  switchOutWork : ℝ

def reservoirControlRead : ReservoirCurrent → ReservoirControlRead
  | .ingress => ⟨Physical.controlHamiltonian, Current.pulse (nativeClockStep : ℝ), nativeClockStep,
      Physical.switchInWork Current.initial, Physical.switchOutWork (Current.supplyNext Current.initial)⟩
  | .running _ => ⟨Physical.baselineHamiltonian, Current.loadPulse (nativeClockStep : ℝ), nativeClockStep, 0, 0⟩

def reservoirEventWork : ReservoirCurrent → ℝ
  | .ingress => Physical.sourceWork Current.initial
  | .running _ => 0

def reservoirAccumulatedWork : ReservoirCurrent → ℝ
  | .ingress => 0
  | .running _ => Physical.sourceWork Current.initial

def reservoirEnergyRead (state : Current.State) : ℝ × ℝ × ℝ × ℝ × ℝ :=
  (Readout.pcEnergy state, Readout.donorEnergy state, EnergyLedger.environmentEnergy state,
    Physical.boundaryEnergy state, Physical.baselineEnergy state)

def reservoirCapacityRead (state : Current.State) : ℝ × ℝ := (Readout.pcCapacity state, Readout.donorAvailable state)

theorem reservoirControl_work (current : ReservoirCurrent) :
    (reservoirControlRead current).switchInWork + (reservoirControlRead current).switchOutWork = reservoirEventWork current := by
  cases current with
  | ingress => rfl
  | running _ => exact add_zero _

theorem reservoirControl_duration (current : ReservoirCurrent) : (reservoirControlRead current).duration = nativeClockStep := by
  cases current <;> rfl

theorem reservoirControl_positive (current : ReservoirCurrent) : 0 < (reservoirControlRead current).duration := by
  rw [reservoirControl_duration]
  exact nativeClockStep_positive

open scoped Matrix.Norms.L2Operator in
theorem reservoirControl_exponential (current : ReservoirCurrent) :
    ((reservoirControlRead current).action : Current.FullJoint) =
      NormedSpace.exp (((reservoirControlRead current).duration : ℝ) •
        (-Complex.I • (reservoirControlRead current).hamiltonian)) := by
  cases current with
  | ingress =>
    change (Current.pulse (nativeClockStep : ℝ) : Current.FullJoint) =
      NormedSpace.exp ((nativeClockStep : ℝ) • (-Complex.I • Physical.controlHamiltonian))
    rw [← Physical.pulse_is_full_flow, Load.Producer.StrictThermal.flowUnitary_matrix_exp]
    simp only [Powered.Dynamics.totalHamiltonian, add_zero, Physical.controlHamiltonian]
  | running _ => exact Physical.loadPulse_baseline _

theorem reservoirNext_joint (current : ReservoirCurrent) :
    (reservoirCurrentState (reservoirNext current)).joint =
      Quantum.conjugation (reservoirControlRead current).action (reservoirCurrentState current).joint := by
  cases current with
  | ingress => exact Current.supplyNext_joint Current.initial
  | running state => exact Current.loadNext_joint state

theorem reservoirNext_clock (current : ReservoirCurrent) :
    (reservoirCurrentState (reservoirNext current)).localClock =
      (reservoirCurrentState current).localClock + nativeClockStep := by cases current <;> rfl

theorem reservoirNext_energyBalance (current : ReservoirCurrent) :
    Physical.baselineEnergy (reservoirCurrentState (reservoirNext current)) -
      Physical.baselineEnergy (reservoirCurrentState current) = reservoirEventWork current := by
  cases current with
  | ingress => exact (Physical.sourceWork_actual Current.initial).symm
  | running state => exact sub_eq_zero.mpr (EnergyLedger.load_preserves_baseline state)

theorem reservoirNext_netAccount (current : ReservoirCurrent) :
    (Thermo.freeEnergy (reservoirCurrentState (reservoirNext current)) - Thermo.freeEnergy (reservoirCurrentState current)) +
      (Current.entropyProduction (reservoirCurrentState (reservoirNext current)) -
        Current.entropyProduction (reservoirCurrentState current)) = reservoirEventWork current := by
  cases current with
  | ingress => exact Thermo.supply_net_account Current.initial
  | running state => exact Thermo.load_net_account state

theorem reservoirAccumulatedWork_next (current : ReservoirCurrent) :
    reservoirAccumulatedWork (reservoirNext current) = reservoirAccumulatedWork current + reservoirEventWork current := by
  cases current with
  | ingress => exact (zero_add _).symm
  | running _ => exact (add_zero _).symm

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
