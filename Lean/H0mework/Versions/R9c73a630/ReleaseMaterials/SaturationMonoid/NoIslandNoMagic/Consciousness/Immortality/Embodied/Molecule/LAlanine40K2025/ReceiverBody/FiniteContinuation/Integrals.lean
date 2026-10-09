import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Dynamics

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
open Propagation.Interface Thermal.Collision Thermal.Quantum
open Thermal.Recovery.Reservoir Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem position_integral (current : Material) (phase : Phase) (i : Coordinate) :
    nuclearPosition current phase duration i-nuclearPosition current phase 0 i=
      ∫ t in (0 : ℝ)..duration, velocity current phase t i := by
  have regular : Continuous (fun t => velocity current phase t i) := by
    cases phase <;> dsimp [velocity,FiniteActuation.onRate,FiniteActuation.offRate,FiniteActuation.rampMomentum,
      FiniteActuation.onTime,FiniteActuation.offTime] <;> fun_prop
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => position_equation current phase t i) (regular.intervalIntegrable 0 duration)).symm

theorem momentum_integral (current : Material) (phase : Phase) (i : Coordinate) :
    nuclearMomentum current phase duration i-nuclearMomentum current phase 0 i=
      ∫ t in (0 : ℝ)..duration, nuclearForce current phase t i := by
  have regular : Continuous (fun t => nuclearForce current phase t i) := by
    cases phase <;> dsimp [nuclearForce,FiniteActuation.onRate,FiniteActuation.offRate,pulseForce,FiniteActuation.progressRate] <;> fun_prop
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => momentum_equation current phase t i) (regular.intervalIntegrable 0 duration)).symm

theorem receiver_integral (current : Material) (phase : Phase) :
    receiver current phase duration-receiver current phase 0=
      ∫ t in (0 : ℝ)..duration, receiverForce current phase t := by
  have regular : Continuous (receiverForce current phase) := by
    cases phase <;> dsimp [receiverForce,kineticRate,FiniteActuation.progress,FiniteActuation.progressRate] <;> fun_prop
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => receiver_equation current phase t) (regular.intervalIntegrable 0 duration)).symm

theorem gamma_integral (current : Material) (phase : Phase) :
    gammaPath current phase duration-gammaPath current phase 0=
      ∫ t in (0 : ℝ)..duration, -Complex.I •
        (FiniteActuation.electronHamiltonian (FiniteActuation.electronicRate phase t)*gammaPath current phase t-
          gammaPath current phase t*FiniteActuation.electronHamiltonian (FiniteActuation.electronicRate phase t)) := by
  have state : Continuous (gammaPath current phase) :=
    continuous_iff_continuousAt.mpr fun t => (gamma_equation current phase t).continuousAt
  have generator : Continuous (fun t => FiniteActuation.electronHamiltonian (FiniteActuation.electronicRate phase t)) := by
    cases phase <;> dsimp [FiniteActuation.electronHamiltonian,FiniteActuation.electronicRate,
      FiniteActuation.onRate,FiniteActuation.offRate] <;> fun_prop
  have regular := ((generator.mul state).sub (state.mul generator)).const_smul (-Complex.I)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => gamma_equation current phase t) (regular.intervalIntegrable 0 duration)).symm

theorem quantum_integral (current : Material) (phase : Phase) :
    quantumPath current phase duration-quantumPath current phase 0=
      ∫ t in (0 : ℝ)..duration, -Complex.I •
        (Pointer.baselineHamiltonian*quantumPath current phase t-quantumPath current phase t*Pointer.baselineHamiltonian) := by
  have state : Continuous (quantumPath current phase) :=
    continuous_iff_continuousAt.mpr fun t => (quantum_equation current phase t).continuousAt
  have regular := ((state.const_mul Pointer.baselineHamiltonian).sub
    (state.mul_const Pointer.baselineHamiltonian)).const_smul (-Complex.I)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => quantum_equation current phase t) (regular.intervalIntegrable 0 duration)).symm

theorem total_momentum_update (current : Material) (valid : Admissible current) (i : Coordinate) :
    ((nextMaterial current).body.frame.momentum i.1 i.2 : ℝ)-(current.body.frame.momentum i.1 i.2 : ℝ)=
      (∫ t in (0 : ℝ)..duration, nuclearForce current .enter t i)+
      (∫ t in (0 : ℝ)..duration, nuclearForce current .drive t i)+
      (∫ t in (0 : ℝ)..duration, nuclearForce current .leave t i) := by
  rw [← momentum_integral,← momentum_integral,← momentum_integral]
  have first := (source_endpoints current valid i).2.1
  have last := (target_endpoints current valid i).2.1
  have join0 := congrFun (state_junctions current).2.2.1 i
  have join1 := congrFun (state_junctions current).2.2.2.1 i
  linarith only [first,last,join0,join1]

theorem total_receiver_update (current : Material) (valid : Admissible current) :
    (nextMaterial current).body.resource.momentum-current.body.resource.momentum=
      (∫ t in (0 : ℝ)..duration, receiverForce current .enter t)+
      (∫ t in (0 : ℝ)..duration, receiverForce current .drive t)+
      (∫ t in (0 : ℝ)..duration, receiverForce current .leave t) := by
  rw [← receiver_integral,← receiver_integral,← receiver_integral]
  have first : receiver current .enter 0=current.body.resource.momentum := rfl
  have last : receiver current .leave duration=(nextMaterial current).body.resource.momentum :=
    (receiver_endpoints current valid).2
  have join0 := (state_junctions current).2.2.2.2.1
  have join1 := (state_junctions current).2.2.2.2.2.1
  linarith only [first,last,join0,join1]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
