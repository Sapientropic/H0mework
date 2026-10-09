import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime.Parent
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Extract.Port.Timeline

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime
open Thermal.Collision Thermal.Quantum Propagation.Interface
open Thermal.Recovery.Reservoir
open Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
open Blocks.EnergyFrame
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] Pointer.baselineHamiltonian resourceBefore

-- The two source clocks have distinct origins. Only elapsed time is shared by this action.
def resourceClock (elapsed : ℝ) : ℝ := (resourceBefore.quantum.localClock : ℝ)+elapsed
def bodyClock (elapsed : ℝ) : ℝ := (bodyResponse.clock : ℝ)+elapsed

def resourcePath (elapsed : ℝ) : PointerJoint :=
  conjugation (Pointer.loadPulse elapsed) resourceBefore.quantum.joint

def jointEnergy (clock receiver : ℝ) (position momentum : Configuration)
    (gamma : Matrix Basis Basis ℂ) (resource : PointerJoint) : ℝ :=
  energy Pointer.baselineHamiltonian resource+completeHamiltonian clock receiver position momentum gamma

theorem resource_path_generated (elapsed : ℝ) :
    resourcePath elapsed=Extract.Port.bodyFlow Pointer.baselineHamiltonian resourceBefore.quantum.joint elapsed := by
  rw [resourcePath,conjugation_apply,Pointer.loadPulse_baseline]
  rfl

theorem resource_equation (elapsed : ℝ) :
    HasDerivAt resourcePath
      (-Complex.I • (Pointer.baselineHamiltonian*resourcePath elapsed-resourcePath elapsed*Pointer.baselineHamiltonian)) elapsed := by
  change HasDerivAt (fun t => resourcePath t) _ elapsed
  simp only [resource_path_generated]
  exact Extract.Port.body_flow_liouville _ _ Pointer.baselineHamiltonian_hermitian elapsed

theorem resource_path_initial : resourcePath 0=resourceBefore.quantum.joint := by
  rw [resource_path_generated]
  simp [Extract.Port.bodyFlow,hamiltonianFlow]

theorem resource_path_target : resourcePath duration=resourceAfter.quantum.joint :=
  (Live.loadNext_joint resourceBefore.quantum).symm

theorem resource_path_energy (elapsed : ℝ) :
    energy Pointer.baselineHamiltonian (resourcePath elapsed)=Live.baselineEnergy resourceBefore.quantum :=
  Extract.Port.Timeline.load_energy_preserved elapsed resourceBefore.quantum.joint

theorem joint_energy_on_path (elapsed : ℝ) :
    jointEnergy elapsed (onPath 1) (positionPath elapsed) (momentumPath elapsed)
      (realizedPath elapsed) (resourcePath elapsed)=
    Live.baselineEnergy resourceBefore.quantum+
      baselineHamiltonian sourcePosition sourceMomentum+Extract.Port.kinetic receiverInitial := by
  rw [jointEnergy,resource_path_energy,complete_hamiltonian_exact,plateau_joint_energy]
  ring

theorem joint_receiver_equation (elapsed : ℝ) :
    HasDerivAt (fun receiver => jointEnergy elapsed receiver (positionPath elapsed)
      (momentumPath elapsed) (realizedPath elapsed) (resourcePath elapsed)) 1 (onPath 1) := by
  simp only [jointEnergy,complete_hamiltonian_exact]
  exact (joint_clock_velocity elapsed).const_add _

theorem joint_clock_equation (elapsed : ℝ) :
    HasDerivAt (fun clock => jointEnergy clock (onPath 1) (positionPath elapsed)
      (momentumPath elapsed) (realizedPath elapsed) (resourcePath elapsed)) 0 elapsed := by
  simp only [jointEnergy,complete_hamiltonian_exact]
  exact (joint_receiver_force elapsed).const_add _

theorem joint_position_equation (elapsed : ℝ) (i : Coordinate) :
    HasDerivAt (fun h => jointEnergy elapsed (onPath 1)
      (Function.update (positionPath elapsed) i (positionPath elapsed i+h)) (momentumPath elapsed)
      (realizedPath elapsed) (resourcePath elapsed)) (-controlForce i) 0 := by
  simp only [jointEnergy,complete_hamiltonian_exact]
  exact (joint_nuclear_force elapsed i).const_add _

theorem joint_momentum_equation (elapsed : ℝ) (i : Coordinate) :
    HasDerivAt (fun h => jointEnergy elapsed (onPath 1) (positionPath elapsed)
      (Function.update (momentumPath elapsed) i (momentumPath elapsed i+h))
      (realizedPath elapsed) (resourcePath elapsed)) 0 0 := by
  simp only [jointEnergy,complete_hamiltonian_exact]
  exact (joint_nuclear_velocity elapsed i).const_add _

theorem clocks_elapsed (elapsed : ℝ) :
    resourceClock elapsed-resourceClock 0=elapsed ∧ bodyClock elapsed-bodyClock 0=elapsed := by
  simp [resourceClock,bodyClock]

theorem clocks_endpoints :
    resourceClock 0=18*duration ∧ resourceClock duration=19*duration ∧
      bodyClock 0=3*duration ∧ bodyClock duration=4*duration := by
  have resource : (resourceBefore.quantum.localClock : ℝ)=18*duration := by
    change (resourceBefore.quantum.localClock : ℝ)=18*(Propagation.Producer.nativeClockStep : ℝ)
    have source : resourceBefore.quantum.localClock=18*Propagation.Producer.nativeClockStep := by
      unfold resourceBefore
      exact input_clocks.1
    exact_mod_cast source
  have body : (bodyResponse.clock : ℝ)=3*duration := by
    change (bodyResponse.clock : ℝ)=3*(Propagation.Producer.nativeClockStep : ℝ)
    exact_mod_cast input_clocks.2
  simp only [resourceClock,bodyClock,resource,body,add_zero]
  constructor
  · trivial
  constructor
  · ring
  constructor
  · trivial
  · ring

theorem elapsed_strictly_forward : 0 < duration := by
  change 0 < (Propagation.Producer.nativeClockStep : ℝ)
  exact_mod_cast Propagation.Producer.nativeClockStep_positive

theorem combined_target_energy :
    energy Pointer.baselineHamiltonian (resourcePath duration)+Extract.Port.kinetic receiverTarget+
      (targetFrame.total : ℝ)=
    Live.baselineEnergy resourceBefore.quantum+Extract.Port.kinetic receiverInitial+
      (Reentry.Producer.targetMomentumKinetic : ℝ)+sourcePotential := by
  rw [resource_path_energy]
  have body := target_mechanical_account
  linarith only [body]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime
