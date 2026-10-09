import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Segments

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
open Propagation.Interface Thermal.Collision Thermal.Quantum
open Thermal.Recovery.Reservoir Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
noncomputable section

def nextKineticQ : ℚ := (1+gainQ)^2*boostedKinetic

def nextFrame : Inertia.Interface.NuclearFrame :=
  { input.joint.body.frame with
    momentum := fun atom axis => targetMomentumQ (atom,axis)
    kinetic := nextKineticQ
    total := nextKineticQ+input.joint.body.frame.potential }

def nextQuantum : Live.State := Live.loadNext (quantumInput .leave)

def generatedBody : Runtime.ActuationResult :=
  { input.joint.body with
    resource := ⟨nextQuantum,receiver .leave duration⟩
    frame := nextFrame
    bodyClock := input.joint.body.bodyClock+3*Propagation.Producer.nativeClockStep }

theorem target_kinetic : (nextKineticQ : ℝ)=nuclearKinetic (plateauMomentum 1) := by
  rw [plateau_kinetic,initial_kinetic_exact]
  simp [nextKineticQ,gain]

theorem target_frame_energy : (nextFrame.total : ℝ)=nuclearKinetic (plateauMomentum 1)+sourcePotential := by
  change ((nextKineticQ+input.joint.body.frame.potential : ℚ) : ℝ)=_
  rw [Rat.cast_add,target_kinetic,input_body]
  rfl

theorem input_frame_energy : (input.joint.body.frame.total : ℝ)=initialKinetic+sourcePotential := by
  rw [input_body,initial_kinetic_exact]
  change ((boostedKinetic+Reentry.Source.stepReadout.nuclear.target.potential : ℚ) : ℝ)=_
  exact Rat.cast_add _ _

theorem source_endpoints (i : Coordinate) :
    nuclearPosition .enter 0 i=(input.joint.body.frame.position i.1 i.2 : ℝ) ∧
    nuclearMomentum .enter 0 i=(input.joint.body.frame.momentum i.1 i.2 : ℝ) ∧
    receiver .enter 0=input.joint.body.resource.momentum ∧
    gammaPath .enter 0=input.joint.body.realized ∧
    quantumPath .enter 0=input.joint.body.resource.quantum.joint := by
  rcases ramp_endpoints with ⟨a,_,_,_,_,_,_,_⟩
  simp only [nuclearPosition,nuclearMomentum,gammaPath,electronicTime,a,ramp_position_zero,
    ramp_momentum_zero,electron_flow_zero,quantum_start,quantumInput,receiver,initialReceiver]
  refine ⟨(input_position i).symm,rfl,?_⟩
  trivial

theorem target_endpoints (i : Coordinate) :
    nuclearPosition .leave duration i=(generatedBody.frame.position i.1 i.2 : ℝ) ∧
    nuclearMomentum .leave duration i=(generatedBody.frame.momentum i.1 i.2 : ℝ) ∧
    receiver .leave duration=generatedBody.resource.momentum ∧
    gammaPath .leave duration=generatedBody.realized ∧
    quantumPath .leave duration=generatedBody.resource.quantum.joint := by
  rcases ramp_endpoints with ⟨_,_,_,_,_,f,_,_⟩
  simp only [nuclearPosition,nuclearMomentum,gammaPath,electronicTime,f,ramp_position_zero,
    ramp_momentum_zero,electron_flow_zero,quantum_finish,generatedBody,nextFrame,nextQuantum]
  refine ⟨(input_position i).symm,target_momentum_rational i,?_⟩
  trivial

theorem target_retains_residual :
    generatedBody.realized=generatedBody.held+generatedBody.inheritedResidual+generatedBody.newNumericalResidual := by
  change input.joint.body.realized=input.joint.body.held+input.joint.body.inheritedResidual+input.joint.body.newNumericalResidual
  rw [input_body]
  exact Runtime.source_output_realization

theorem target_momentum_changed : generatedBody.frame.momentum ≠ input.joint.body.frame.momentum := by
  intro same
  have momenta : plateauMomentum 1=initialMomentum := by
    funext i
    rw [target_momentum_rational]
    change (generatedBody.frame.momentum i.1 i.2 : ℝ)=_
    rw [same]
    rfl
  have positive := target_debit_positive_and_bounded.1
  rw [momenta] at positive
  change 0 < initialKinetic-initialKinetic at positive
  linarith only [positive]

theorem target_stock : initialReceiver/2 < generatedBody.resource.momentum :=
  plateau_receiver_positive 1 (by norm_num) (by norm_num)

theorem target_mechanical_account :
    Extract.Port.kinetic generatedBody.resource.momentum+(generatedBody.frame.total : ℝ)=
      Extract.Port.kinetic input.joint.body.resource.momentum+(input.joint.body.frame.total : ℝ) := by
  have positive : 0 < plateauReceiver 1 := (half_pos initial_receiver_positive).trans target_stock
  change Extract.Port.kinetic (plateauReceiver 1)+(nextFrame.total : ℝ)=
    Extract.Port.kinetic initialReceiver+(input.joint.body.frame.total : ℝ)
  rw [target_frame_energy,input_frame_energy,Extract.Port.kinetic,Extract.Port.kinetic,
    abs_of_pos positive,abs_of_pos initial_receiver_positive,plateauReceiver]
  ring

theorem target_resource_account :
    Live.baselineEnergy generatedBody.resource.quantum+Extract.Port.kinetic generatedBody.resource.momentum+
      (generatedBody.frame.total : ℝ)=
    Live.baselineEnergy input.joint.body.resource.quantum+Extract.Port.kinetic input.joint.body.resource.momentum+
      (input.joint.body.frame.total : ℝ) := by
  have resource : Live.baselineEnergy generatedBody.resource.quantum=Live.baselineEnergy input.joint.body.resource.quantum := by
    change Live.baselineEnergy nextQuantum=_
    simp only [nextQuantum,quantumInput,Live.loadNext_preserves_baseline]
  rw [resource,add_assoc,target_mechanical_account,← add_assoc]

theorem target_free_energy_entropy_account :
    Live.freeEnergy generatedBody.resource.quantum+Live.entropyProduction generatedBody.resource.quantum+
      Extract.Port.kinetic generatedBody.resource.momentum+(generatedBody.frame.total : ℝ)=
    Live.freeEnergy input.joint.body.resource.quantum+Live.entropyProduction input.joint.body.resource.quantum+
      Extract.Port.kinetic input.joint.body.resource.momentum+(input.joint.body.frame.total : ℝ) := by
  have step0 := Live.loadNext_net_account input.joint.body.resource.quantum
  have step1 := Live.loadNext_net_account (Live.loadNext input.joint.body.resource.quantum)
  have step2 := Live.loadNext_net_account (Live.loadNext (Live.loadNext input.joint.body.resource.quantum))
  have body := target_mechanical_account
  change Live.freeEnergy nextQuantum+Live.entropyProduction nextQuantum+_+_=_
  dsimp only [nextQuantum,quantumInput]
  linarith only [step0,step1,step2,body]

theorem generated_clocks :
    generatedBody.resource.quantum.localClock=22*Propagation.Producer.nativeClockStep ∧
    generatedBody.bodyClock=7*Propagation.Producer.nativeClockStep := by
  have current := Coulomb.Runtime.actual_clocks.2
  change input.joint.body.resource.quantum.localClock=19*Propagation.Producer.nativeClockStep ∧
    input.joint.body.bodyClock=4*Propagation.Producer.nativeClockStep at current
  constructor
  · change nextQuantum.localClock=_
    rw [nextQuantum,quantumInput,Live.loadNext_clock,Live.loadNext_clock,Live.loadNext_clock,current.1]
    ring
  · change input.joint.body.bodyClock+3*Propagation.Producer.nativeClockStep=_
    rw [current.2]
    ring

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
