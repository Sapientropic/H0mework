import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Junctions

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
open Propagation.Interface Thermal.Collision Thermal.Quantum
open Thermal.Recovery.Reservoir Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
noncomputable section

def velocity (current : Material) : Phase → ℝ → Configuration
  | .enter => fun t i => FiniteActuation.onRate t*FiniteActuation.rampMomentum (momentum current) (FiniteActuation.onTime t) i/mass i
  | .drive => fun _ _ => 0
  | .leave => fun t i => FiniteActuation.offRate t*FiniteActuation.rampMomentum (pulseMomentum current 1) (FiniteActuation.offTime t) i/mass i

def nuclearForce (current : Material) : Phase → ℝ → Configuration
  | .enter => fun t i => FiniteActuation.onRate t*sourceForce i
  | .drive => pulseForce current
  | .leave => fun t i => FiniteActuation.offRate t*sourceForce i

def receiverForce (current : Material) : Phase → ℝ → ℝ
  | .enter => fun _ => 0
  | .drive => fun t => -kineticRate current t
  | .leave => fun _ => 0

theorem position_equation (current : Material) (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => nuclearPosition current phase time i) (velocity current phase t i) t := by
  cases phase with
  | enter => exact FiniteActuation.ramp_position_derivative _ _ _ _ _ (FiniteActuation.on_time_derivative t) rfl i
  | drive => exact hasDerivAt_const t _
  | leave => exact FiniteActuation.ramp_position_derivative _ _ _ _ _ (FiniteActuation.off_time_derivative t) rfl i

theorem momentum_equation (current : Material) (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => nuclearMomentum current phase time i) (nuclearForce current phase t i) t := by
  cases phase with
  | enter => exact FiniteActuation.ramp_momentum_derivative _ _ _ _ (FiniteActuation.on_time_derivative t) i
  | drive => exact momentum_derivative current t i
  | leave => exact FiniteActuation.ramp_momentum_derivative _ _ _ _ (FiniteActuation.off_time_derivative t) i

theorem receiver_equation (current : Material) (phase : Phase) (t : ℝ) :
    HasDerivAt (receiver current phase) (receiverForce current phase t) t := by
  cases phase with
  | enter => exact hasDerivAt_const t _
  | drive => exact receiver_derivative current t
  | leave => exact hasDerivAt_const t _

theorem nuclear_position_partial (current : Material) (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => nuclearEnergy current phase t
      (Function.update (nuclearPosition current phase t) i (nuclearPosition current phase t i+x)) (nuclearMomentum current phase t))
        (-nuclearForce current phase t i) 0 := by
  cases phase with
  | enter => simpa only [nuclearEnergy,nuclearPosition,nuclearMomentum,nuclearForce,neg_mul] using
      FiniteActuation.ramp_position_partial (momentum current) (FiniteActuation.onTime t) (FiniteActuation.onRate t) i
  | drive => exact pulse_position_partial current t i
  | leave => simpa only [nuclearEnergy,nuclearPosition,nuclearMomentum,nuclearForce,neg_mul] using
      FiniteActuation.ramp_position_partial (pulseMomentum current 1) (FiniteActuation.offTime t) (FiniteActuation.offRate t) i

theorem nuclear_momentum_partial (current : Material) (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => nuclearEnergy current phase t (nuclearPosition current phase t)
      (Function.update (nuclearMomentum current phase t) i (nuclearMomentum current phase t i+x))) (velocity current phase t i) 0 := by
  cases phase with
  | enter => exact FiniteActuation.ramp_momentum_partial (momentum current) (FiniteActuation.onTime t) (FiniteActuation.onRate t) i
  | drive => exact pulse_momentum_partial current t i
  | leave => exact FiniteActuation.ramp_momentum_partial (pulseMomentum current 1) (FiniteActuation.offTime t) (FiniteActuation.offRate t) i

theorem nuclear_clock_partial (current : Material) (phase : Phase) (t : ℝ) :
    HasDerivAt (fun time => nuclearEnergy current phase time (nuclearPosition current phase t) (nuclearMomentum current phase t))
      (-receiverForce current phase t) t := by
  cases phase with
  | enter => simpa only [receiverForce,nuclearEnergy,nuclearPosition,nuclearMomentum,neg_zero] using!
      FiniteActuation.on_clock_derivative (momentum current) t
  | drive => simpa only [receiverForce,nuclearEnergy,nuclearPosition,nuclearMomentum,neg_neg] using!
      pulse_clock_partial current t
  | leave => simpa only [receiverForce,nuclearEnergy,nuclearPosition,nuclearMomentum,neg_zero] using!
      FiniteActuation.off_clock_derivative (pulseMomentum current 1) t

theorem joint_clock_partial (current : Material) (valid : Admissible current) (phase : Phase) (t : ℝ) :
    HasDerivAt (fun time => jointHamiltonian current phase time (receiver current phase t) (nuclearPosition current phase t)
      (nuclearMomentum current phase t) (gammaPath current phase t) (quantumPath current phase t)) (-receiverForce current phase t) t := by
  simp only [jointHamiltonian,gamma_centered_energy current valid,mul_zero,add_zero]
  exact (nuclear_clock_partial current phase t).const_add _

theorem joint_receiver_partial (current : Material) (valid : Admissible current) (phase : Phase) (t : ℝ)
    (lo : 0 ≤ t) (hi : t ≤ duration) :
    HasDerivAt (fun reserve => jointHamiltonian current phase t reserve (nuclearPosition current phase t)
      (nuclearMomentum current phase t) (gammaPath current phase t) (quantumPath current phase t)) 1 (receiver current phase t) := by
  unfold jointHamiltonian Extract.Port.kinetic
  exact (((hasDerivAt_abs_pos (receiver_positive current valid phase t lo hi)).const_add _).add_const _).add_const _

theorem joint_nuclear_force (current : Material) (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => jointHamiltonian current phase t (receiver current phase t)
      (Function.update (nuclearPosition current phase t) i (nuclearPosition current phase t i+x)) (nuclearMomentum current phase t)
      (gammaPath current phase t) (quantumPath current phase t)) (-nuclearForce current phase t i) 0 := by
  unfold jointHamiltonian
  exact ((nuclear_position_partial current phase t i).const_add _).add_const _

theorem joint_nuclear_velocity (current : Material) (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => jointHamiltonian current phase t (receiver current phase t) (nuclearPosition current phase t)
      (Function.update (nuclearMomentum current phase t) i (nuclearMomentum current phase t i+x))
      (gammaPath current phase t) (quantumPath current phase t)) (velocity current phase t i) 0 := by
  unfold jointHamiltonian
  exact ((nuclear_momentum_partial current phase t i).const_add _).add_const _

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
