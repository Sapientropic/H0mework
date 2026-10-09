import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime.PointerLedger

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime

open Propagation.Producer
open scoped ComplexOrder
noncomputable section

structure PointerControlRead where
  hamiltonian : PointerJoint
  action : Matrix.unitaryGroup PointerIndex ℂ
  duration : ℚ
  switchInWork : ℝ
  switchOutWork : ℝ

def pointerControlRead : PointerCurrent → PointerControlRead
  | .ingress => ⟨sourceHamiltonian, sourceUnitary, nativeClockStep,
      Live.switchInWork Live.initial, Live.switchOutWork Live.first⟩
  | .running _ => ⟨Pointer.baselineHamiltonian, Pointer.loadPulse (nativeClockStep : ℝ), nativeClockStep, 0, 0⟩

def pointerEventWork : PointerCurrent → ℝ
  | .ingress => Live.measurementWork Live.initial
  | .running _ => 0

def pointerAccumulatedWork : PointerCurrent → ℝ
  | .ingress => 0
  | .running _ => Live.measurementWork Live.initial

def pointerMatrix (joint : PointerJoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  Powered.Dynamics.controllerReduce (joint.submatrix pointerIncidence.symm pointerIncidence.symm)

def pointerEnergyRead (state : Live.State) : ℝ × ℝ × ℝ × ℝ :=
  (Live.baselineEnergy state, Collision.energy Physical.baselineHamiltonian (bodyRead state.joint),
    pointerEnergy state.joint, Live.environmentEnergy state)

theorem pointerControl_work (current : PointerCurrent) :
    (pointerControlRead current).switchInWork + (pointerControlRead current).switchOutWork = pointerEventWork current := by
  cases current with
  | ingress => rfl
  | running _ => exact add_zero _

theorem pointerControl_positive (current : PointerCurrent) : 0 < (pointerControlRead current).duration := by
  cases current <;> exact nativeClockStep_positive

open scoped Matrix.Norms.L2Operator in
theorem pointerControl_exponential (current : PointerCurrent) :
    ((pointerControlRead current).action : PointerJoint) =
      NormedSpace.exp (((pointerControlRead current).duration : ℝ) •
        (-Complex.I • (pointerControlRead current).hamiltonian)) := by
  cases current with
  | ingress => exact sourceHamiltonian_generates.symm
  | running _ => exact loadPulse_baseline _

theorem pointerControl_action (current : PointerCurrent) : (pointerControlRead current).action = pointerAction current := by
  cases current <;> rfl

theorem pointerNext_energyBalance (current : PointerCurrent) :
    Live.baselineEnergy (pointerCurrentState (pointerNext current)) -
      Live.baselineEnergy (pointerCurrentState current) = pointerEventWork current := by
  cases current with
  | ingress => exact (Live.measurementWork_actual Live.initial).symm
  | running state => exact sub_eq_zero.mpr (Live.loadNext_preserves_baseline state)

theorem pointerNext_netAccount (current : PointerCurrent) :
    (Live.freeEnergy (pointerCurrentState (pointerNext current)) - Live.freeEnergy (pointerCurrentState current)) +
      (Live.entropyProduction (pointerCurrentState (pointerNext current)) -
        Live.entropyProduction (pointerCurrentState current)) = pointerEventWork current := by
  cases current with
  | ingress => exact Live.measureNext_net_account Live.initial
  | running state => exact Live.loadNext_net_account state

theorem pointerAccumulatedWork_next (current : PointerCurrent) :
    pointerAccumulatedWork (pointerNext current) = pointerAccumulatedWork current + pointerEventWork current := by
  cases current with
  | ingress => exact (zero_add _).symm
  | running _ => exact (add_zero _).symm

theorem pointerMatrix_positive (state : Live.State) : (pointerMatrix state.joint).PosSemidef :=
  Powered.Dynamics.controllerReduce_posSemidef _ (state.positive.submatrix _)

theorem pointerMatrix_trace (state : Live.State) : (pointerMatrix state.joint).trace = 1 :=
  (Powered.Dynamics.controllerReduce_trace _).trans
    ((submatrix_equiv_trace _ pointerIncidence.symm).trans state.normalized)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
