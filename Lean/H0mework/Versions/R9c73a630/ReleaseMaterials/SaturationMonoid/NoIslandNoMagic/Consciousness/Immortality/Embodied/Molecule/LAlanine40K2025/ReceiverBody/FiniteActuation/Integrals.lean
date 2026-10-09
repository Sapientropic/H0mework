import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Dynamics
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Outcome

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
open Propagation.Interface Thermal.Collision Thermal.Quantum
open Thermal.Recovery.Reservoir Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem position_integral (phase : Phase) (i : Coordinate) :
    nuclearPosition phase duration i-nuclearPosition phase 0 i=∫ t in (0 : ℝ)..duration, velocity phase t i := by
  have regular : Continuous (fun t => velocity phase t i) := by
    cases phase <;> dsimp [velocity,onRate,offRate,rampMomentum,onTime,offTime] <;> fun_prop
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => position_equation phase t i) (regular.intervalIntegrable 0 duration)).symm

theorem momentum_integral (phase : Phase) (i : Coordinate) :
    nuclearMomentum phase duration i-nuclearMomentum phase 0 i=∫ t in (0 : ℝ)..duration, nuclearForce phase t i := by
  have regular : Continuous (fun t => nuclearForce phase t i) := by
    cases phase <;> dsimp [nuclearForce,onRate,offRate,plateauForce,progressRate] <;> fun_prop
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => momentum_equation phase t i) (regular.intervalIntegrable 0 duration)).symm

theorem receiver_integral (phase : Phase) :
    receiver phase duration-receiver phase 0=∫ t in (0 : ℝ)..duration, receiverForce phase t := by
  have regular : Continuous (receiverForce phase) := by
    cases phase <;> dsimp [receiverForce,kineticRate,progress,progressRate] <;> fun_prop
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => receiver_equation phase t) (regular.intervalIntegrable 0 duration)).symm

theorem gamma_integral (phase : Phase) :
    gammaPath phase duration-gammaPath phase 0=
      ∫ t in (0 : ℝ)..duration, -Complex.I •
        (electronHamiltonian (electronicRate phase t)*gammaPath phase t-
          gammaPath phase t*electronHamiltonian (electronicRate phase t)) := by
  have state : Continuous (gammaPath phase) :=
    continuous_iff_continuousAt.mpr fun t => (gamma_equation phase t).continuousAt
  have generator : Continuous (fun t => electronHamiltonian (electronicRate phase t)) := by
    cases phase <;> dsimp [electronHamiltonian,electronicRate,onRate,offRate] <;> fun_prop
  have regular := ((generator.mul state).sub (state.mul generator)).const_smul (-Complex.I)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => gamma_equation phase t) (regular.intervalIntegrable 0 duration)).symm

theorem quantum_integral (phase : Phase) :
    quantumPath phase duration-quantumPath phase 0=
      ∫ t in (0 : ℝ)..duration, -Complex.I •
        (Pointer.baselineHamiltonian*quantumPath phase t-quantumPath phase t*Pointer.baselineHamiltonian) := by
  have state : Continuous (quantumPath phase) :=
    continuous_iff_continuousAt.mpr fun t => (quantum_equation phase t).continuousAt
  have regular := ((state.const_mul Pointer.baselineHamiltonian).sub
    (state.mul_const Pointer.baselineHamiltonian)).const_smul (-Complex.I)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => quantum_equation phase t) (regular.intervalIntegrable 0 duration)).symm

theorem total_momentum_update (i : Coordinate) :
    (generatedBody.frame.momentum i.1 i.2 : ℝ)-(input.joint.body.frame.momentum i.1 i.2 : ℝ)=
      (∫ t in (0 : ℝ)..duration, nuclearForce .enter t i)+
      (∫ t in (0 : ℝ)..duration, nuclearForce .drive t i)+
      (∫ t in (0 : ℝ)..duration, nuclearForce .leave t i) := by
  rw [← momentum_integral,← momentum_integral,← momentum_integral]
  have first := (source_endpoints i).2.1
  have last := (target_endpoints i).2.1
  have join0 := congrFun state_junctions.2.2.1 i
  have join1 := congrFun state_junctions.2.2.2.1 i
  linarith only [first,last,join0,join1]

theorem total_receiver_update :
    generatedBody.resource.momentum-input.joint.body.resource.momentum=
      (∫ t in (0 : ℝ)..duration, receiverForce .enter t)+
      (∫ t in (0 : ℝ)..duration, receiverForce .drive t)+
      (∫ t in (0 : ℝ)..duration, receiverForce .leave t) := by
  rw [← receiver_integral,← receiver_integral,← receiver_integral]
  have first : receiver .enter 0=input.joint.body.resource.momentum := rfl
  have last : receiver .leave duration=generatedBody.resource.momentum := rfl
  have join0 := state_junctions.2.2.2.2.1
  have join1 := state_junctions.2.2.2.2.2.1
  linarith only [first,last,join0,join1]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
