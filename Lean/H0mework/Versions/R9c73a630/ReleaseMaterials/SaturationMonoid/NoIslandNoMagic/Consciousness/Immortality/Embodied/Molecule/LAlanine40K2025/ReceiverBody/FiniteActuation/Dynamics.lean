import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Segments

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
open Propagation.Interface Thermal.Collision Thermal.Quantum
open Thermal.Recovery.Reservoir Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
noncomputable section

def velocity : Phase → ℝ → Configuration
  | .enter => fun t i => onRate t*rampMomentum initialMomentum (onTime t) i/mass i
  | .drive => fun _ _ => 0
  | .leave => fun t i => offRate t*rampMomentum (plateauMomentum 1) (offTime t) i/mass i

def nuclearForce : Phase → ℝ → Configuration
  | .enter => fun t i => onRate t*sourceForce i
  | .drive => plateauForce
  | .leave => fun t i => offRate t*sourceForce i

def receiverForce : Phase → ℝ → ℝ
  | .enter => fun _ => 0
  | .drive => fun t => -kineticRate t
  | .leave => fun _ => 0

theorem position_equation (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => nuclearPosition phase time i) (velocity phase t i) t := by
  cases phase with
  | enter => exact ramp_position_derivative _ _ _ _ _ (on_time_derivative t) rfl i
  | drive => exact hasDerivAt_const t _
  | leave => exact ramp_position_derivative _ _ _ _ _ (off_time_derivative t) rfl i

theorem momentum_equation (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => nuclearMomentum phase time i) (nuclearForce phase t i) t := by
  cases phase with
  | enter => exact ramp_momentum_derivative _ _ _ _ (on_time_derivative t) i
  | drive => exact plateau_momentum_time_derivative t i
  | leave => exact ramp_momentum_derivative _ _ _ _ (off_time_derivative t) i

theorem receiver_equation (phase : Phase) (t : ℝ) :
    HasDerivAt (receiver phase) (receiverForce phase t) t := by
  cases phase with
  | enter => exact hasDerivAt_const t _
  | drive => exact plateau_receiver_derivative t
  | leave => exact hasDerivAt_const t _

theorem nuclear_position_partial (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => nuclearEnergy phase t
      (Function.update (nuclearPosition phase t) i (nuclearPosition phase t i+x)) (nuclearMomentum phase t))
        (-nuclearForce phase t i) 0 := by
  cases phase with
  | enter => simpa only [nuclearEnergy,nuclearPosition,nuclearMomentum,nuclearForce,neg_mul] using
      ramp_position_partial initialMomentum (onTime t) (onRate t) i
  | drive => exact plateau_position_partial t i
  | leave => simpa only [nuclearEnergy,nuclearPosition,nuclearMomentum,nuclearForce,neg_mul] using
      ramp_position_partial (plateauMomentum 1) (offTime t) (offRate t) i

theorem nuclear_momentum_partial (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => nuclearEnergy phase t (nuclearPosition phase t)
      (Function.update (nuclearMomentum phase t) i (nuclearMomentum phase t i+x))) (velocity phase t i) 0 := by
  cases phase with
  | enter => exact ramp_momentum_partial initialMomentum (onTime t) (onRate t) i
  | drive => exact plateau_momentum_partial t i
  | leave => exact ramp_momentum_partial (plateauMomentum 1) (offTime t) (offRate t) i

theorem nuclear_clock_partial (phase : Phase) (t : ℝ) :
    HasDerivAt (fun time => nuclearEnergy phase time (nuclearPosition phase t) (nuclearMomentum phase t))
      (-receiverForce phase t) t := by
  cases phase with
  | enter => simpa only [receiverForce,nuclearEnergy,nuclearPosition,nuclearMomentum,neg_zero] using! on_clock_derivative initialMomentum t
  | drive => simpa only [receiverForce,nuclearEnergy,nuclearPosition,nuclearMomentum,neg_neg] using! plateau_clock_partial t
  | leave => simpa only [receiverForce,nuclearEnergy,nuclearPosition,nuclearMomentum,neg_zero] using! off_clock_derivative (plateauMomentum 1) t

theorem joint_clock_partial (phase : Phase) (t : ℝ) :
    HasDerivAt (fun time => jointHamiltonian phase time (receiver phase t) (nuclearPosition phase t)
      (nuclearMomentum phase t) (gammaPath phase t) (quantumPath phase t)) (-receiverForce phase t) t := by
  have electronic : referenceElectronicEnergy (gammaPath phase t)=0 := electron_centered_energy _
  simp only [jointHamiltonian,electronic,mul_zero,add_zero]
  exact (nuclear_clock_partial phase t).const_add _

theorem joint_receiver_partial (phase : Phase) (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ duration) :
    HasDerivAt (fun reserve => jointHamiltonian phase t reserve (nuclearPosition phase t)
      (nuclearMomentum phase t) (gammaPath phase t) (quantumPath phase t)) 1 (receiver phase t) := by
  unfold jointHamiltonian Extract.Port.kinetic
  exact (((hasDerivAt_abs_pos (receiver_positive phase t lo hi)).const_add _).add_const _).add_const _

theorem joint_nuclear_force (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => jointHamiltonian phase t (receiver phase t)
      (Function.update (nuclearPosition phase t) i (nuclearPosition phase t i+x)) (nuclearMomentum phase t)
      (gammaPath phase t) (quantumPath phase t)) (-nuclearForce phase t i) 0 := by
  unfold jointHamiltonian
  exact ((nuclear_position_partial phase t i).const_add _).add_const _

theorem joint_nuclear_velocity (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => jointHamiltonian phase t (receiver phase t) (nuclearPosition phase t)
      (Function.update (nuclearMomentum phase t) i (nuclearMomentum phase t i+x))
      (gammaPath phase t) (quantumPath phase t)) (velocity phase t i) 0 := by
  unfold jointHamiltonian
  exact ((nuclear_momentum_partial phase t i).const_add _).add_const _

theorem clock_junctions : phaseOffset .enter+duration=phaseOffset .drive ∧
    phaseOffset .drive+duration=phaseOffset .leave ∧ phaseOffset .leave+duration=3*duration := by
  dsimp [phaseOffset]
  constructor
  · ring
  constructor <;> ring

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
