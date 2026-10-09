import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Nuclear

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
open FiniteContinuation Propagation.Interface Thermal.Quantum
open Thermal.Recovery.Reservoir.Pointer
noncomputable section

def unscale (unit : ℝ) (value : Configuration) : Configuration := fun i => value i/unit

theorem unscale_update (unit : ℝ) (value : Configuration) (i : Coordinate) (delta : ℝ) :
    unscale unit (Function.update value i (value i+delta))=
      Function.update (unscale unit value) i (unscale unit value i+delta/unit) := by
  funext j
  by_cases same : j=i <;> simp [unscale,Function.update_apply,same,add_div]

theorem position_unscale (current : Material) (phase : Phase) (second : ℝ) :
    unscale lengthMeter (positionMeter current phase second)=nuclearPosition current phase (second/timeSecond) := by
  funext i
  unfold unscale positionMeter
  field_simp [length_positive.ne']

theorem momentum_unscale (current : Material) (phase : Phase) (second : ℝ) :
    unscale momentumSI (momentumPathSI current phase second)=nuclearMomentum current phase (second/timeSecond) := by
  funext i
  unfold unscale momentumPathSI
  field_simp [momentum_positive.ne']

theorem receiver_unscale (current : Material) (phase : Phase) (second : ℝ) :
    receiverJoule current phase second/energyJoule=receiver current phase (second/timeSecond) := by
  unfold receiverJoule
  field_simp [energy_positive.ne']

def jointHamiltonianSI (current : Material) (phase : Phase) (second receiverEnergy : ℝ)
    (position momentum : Configuration) (gamma : Matrix Basis Basis ℂ) (resource : PointerJoint) : ℝ :=
  energyJoule*FiniteContinuation.jointHamiltonian current phase (second/timeSecond) (receiverEnergy/energyJoule)
    (unscale lengthMeter position) (unscale momentumSI momentum) gamma resource

theorem joint_force_si (current : Material) (phase : Phase) (second : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => jointHamiltonianSI current phase second (receiverJoule current phase second)
      (Function.update (positionMeter current phase second) i (positionMeter current phase second i+x))
      (momentumPathSI current phase second) (gammaPath current phase (second/timeSecond))
      (quantumPath current phase (second/timeSecond))) (-forceNewton current phase second i) 0 := by
  simp_rw [jointHamiltonianSI,receiver_unscale,unscale_update,position_unscale,momentum_unscale]
  have base := FiniteContinuation.joint_nuclear_force current phase (second/timeSecond) i
  have atZero : HasDerivAt (fun x => FiniteContinuation.jointHamiltonian current phase (second/timeSecond)
      (receiver current phase (second/timeSecond))
      (Function.update (nuclearPosition current phase (second/timeSecond)) i (nuclearPosition current phase (second/timeSecond) i+x))
      (nuclearMomentum current phase (second/timeSecond)) (gammaPath current phase (second/timeSecond))
      (quantumPath current phase (second/timeSecond))) (-nuclearForce current phase (second/timeSecond) i) (0/lengthMeter) := by
    simpa only [zero_div] using base
  have generated := (atZero.comp 0 ((hasDerivAt_id 0).div_const lengthMeter)).const_mul energyJoule
  unfold forceNewton
  rw [momentum_rate_units]
  convert generated using 1 <;> first | rfl | ring

theorem joint_velocity_si (current : Material) (phase : Phase) (second : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => jointHamiltonianSI current phase second (receiverJoule current phase second)
      (positionMeter current phase second)
      (Function.update (momentumPathSI current phase second) i (momentumPathSI current phase second i+x))
      (gammaPath current phase (second/timeSecond)) (quantumPath current phase (second/timeSecond)))
      (velocitySI current phase second i) 0 := by
  simp_rw [jointHamiltonianSI,receiver_unscale,unscale_update,position_unscale,momentum_unscale]
  have base := FiniteContinuation.joint_nuclear_velocity current phase (second/timeSecond) i
  have atZero : HasDerivAt (fun x => FiniteContinuation.jointHamiltonian current phase (second/timeSecond)
      (receiver current phase (second/timeSecond)) (nuclearPosition current phase (second/timeSecond))
      (Function.update (nuclearMomentum current phase (second/timeSecond)) i (nuclearMomentum current phase (second/timeSecond) i+x))
      (gammaPath current phase (second/timeSecond)) (quantumPath current phase (second/timeSecond)))
      (velocity current phase (second/timeSecond) i) (0/momentumSI) := by
    simpa only [zero_div] using base
  have generated := (atZero.comp 0 ((hasDerivAt_id 0).div_const momentumSI)).const_mul energyJoule
  unfold velocitySI
  rw [← hamilton_velocity_units]
  convert generated using 1 <;> first | rfl | ring

theorem joint_clock_si (current : Material) (valid : Admissible current) (phase : Phase) (second : ℝ) :
    HasDerivAt (fun time => jointHamiltonianSI current phase time (receiverJoule current phase second)
      (positionMeter current phase second) (momentumPathSI current phase second)
      (gammaPath current phase (second/timeSecond)) (quantumPath current phase (second/timeSecond)))
      (-receiverPower current phase second) second := by
  simp_rw [jointHamiltonianSI,receiver_unscale,position_unscale,momentum_unscale]
  have generated := ((joint_clock_partial current valid phase (second/timeSecond)).comp second
    ((hasDerivAt_id second).div_const timeSecond)).const_mul energyJoule
  unfold receiverPower
  convert generated using 1 <;> first | rfl | ring

theorem clock_range (second : ℝ) (lo : 0 ≤ second) (hi : second ≤ segmentSeconds) :
    0 ≤ second/timeSecond ∧ second/timeSecond ≤ duration := by
  refine ⟨div_nonneg lo time_positive.le,?_⟩
  exact (div_le_iff₀ time_positive).2 hi

theorem joint_receiver_si (current : Material) (valid : Admissible current) (phase : Phase) (second : ℝ)
    (lo : 0 ≤ second) (hi : second ≤ segmentSeconds) :
    HasDerivAt (fun reserve => jointHamiltonianSI current phase second reserve
      (positionMeter current phase second) (momentumPathSI current phase second)
      (gammaPath current phase (second/timeSecond)) (quantumPath current phase (second/timeSecond)))
      1 (receiverJoule current phase second) := by
  simp_rw [jointHamiltonianSI,position_unscale,momentum_unscale]
  have base := joint_receiver_partial current valid phase (second/timeSecond)
    (clock_range second lo hi).1 (clock_range second lo hi).2
  rw [← receiver_unscale current phase second] at base
  have generated := (base.comp (receiverJoule current phase second)
    ((hasDerivAt_id _).div_const energyJoule)).const_mul energyJoule
  convert generated using 1 <;> first | rfl | field_simp [energy_positive.ne']

theorem joint_energy_si (current : Material) (valid : Admissible current) (phase : Phase) (second : ℝ)
    (lo : 0 ≤ second) (hi : second ≤ segmentSeconds) :
    jointHamiltonianSI current phase second (receiverJoule current phase second)
      (positionMeter current phase second) (momentumPathSI current phase second)
      (gammaPath current phase (second/timeSecond)) (quantumPath current phase (second/timeSecond))=
      energyJoule*(Live.baselineEnergy current.body.resource.quantum+current.body.resource.momentum+
        nuclearKinetic (momentum current)+sourcePotential) := by
  rw [jointHamiltonianSI,receiver_unscale,position_unscale,momentum_unscale,
    phase_energy_account current valid phase (second/timeSecond) (clock_range second lo hi).1 (clock_range second lo hi).2]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
