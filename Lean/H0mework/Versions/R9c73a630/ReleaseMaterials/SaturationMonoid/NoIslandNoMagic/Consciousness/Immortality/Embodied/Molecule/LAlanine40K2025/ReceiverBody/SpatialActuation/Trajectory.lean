import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Source

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
noncomputable section

def shift : Phase → ℝ → Configuration
  | .enter => fun _ _ => 0
  | .drive => fun t i => displacement i*FiniteActuation.progress t
  | .leave => fun _ => displacement

def shiftRate : Phase → ℝ → Configuration
  | .enter => fun _ _ => 0
  | .drive => fun t i => displacement i*FiniteActuation.progressRate t
  | .leave => fun _ _ => 0

def position (phase : Phase) (t : ℝ) : Configuration :=
  FiniteContinuation.nuclearPosition input phase t+shift phase t

def velocity (phase : Phase) (t : ℝ) : Configuration :=
  FiniteContinuation.velocity input phase t+shiftRate phase t

def momentum (phase : Phase) (t : ℝ) : Configuration :=
  FiniteContinuation.nuclearMomentum input phase t

def force (phase : Phase) (t : ℝ) : Configuration :=
  FiniteContinuation.nuclearForce input phase t

def receiver (phase : Phase) (t : ℝ) : ℝ := FiniteContinuation.receiver input phase t
def receiverForce (phase : Phase) (t : ℝ) : ℝ := FiniteContinuation.receiverForce input phase t

theorem shift_derivative (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => shift phase time i) (shiftRate phase t i) t := by
  cases phase with
  | enter => exact hasDerivAt_const t 0
  | drive => exact (FiniteActuation.progress_derivative t).const_mul (displacement i)
  | leave => exact hasDerivAt_const t _

theorem position_equation (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => position phase time i) (velocity phase t i) t :=
  (FiniteContinuation.position_equation input phase t i).add (shift_derivative phase t i)

theorem momentum_equation (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => momentum phase time i) (force phase t i) t :=
  FiniteContinuation.momentum_equation input phase t i

theorem receiver_equation (phase : Phase) (t : ℝ) :
    HasDerivAt (receiver phase) (receiverForce phase t) t :=
  FiniteContinuation.receiver_equation input phase t

theorem velocity_differentiable (phase : Phase) (i : Coordinate) :
    Differentiable ℝ (fun t => velocity phase t i) := by
  unfold velocity FiniteContinuation.velocity shiftRate
  cases phase <;> dsimp only [Pi.add_apply,FiniteActuation.onRate,FiniteActuation.offRate,
    FiniteActuation.rampMomentum,FiniteActuation.onTime,FiniteActuation.offTime,
    FiniteActuation.progressRate] <;> fun_prop

theorem force_differentiable (phase : Phase) (i : Coordinate) :
    Differentiable ℝ (fun t => force phase t i) := by
  unfold force FiniteContinuation.nuclearForce
  cases phase <;> dsimp only [FiniteActuation.onRate,FiniteActuation.offRate,
    FiniteContinuation.pulseForce,FiniteActuation.progressRate] <;> fun_prop

theorem shift_junctions :
    shift .enter duration=shift .drive 0 ∧ shift .drive duration=shift .leave 0 ∧
    shiftRate .enter duration=shiftRate .drive 0 ∧ shiftRate .drive duration=shiftRate .leave 0 := by
  simp only [shift,shiftRate,FiniteActuation.progress_endpoints.1,
    FiniteActuation.progress_endpoints.2,FiniteActuation.progress_rate_endpoints.1,
    FiniteActuation.progress_rate_endpoints.2,mul_zero,mul_one]
  trivial

theorem position_junctions :
    position .enter duration=position .drive 0 ∧ position .drive duration=position .leave 0 := by
  rcases FiniteContinuation.state_junctions input with ⟨a,b,_⟩
  exact ⟨by rw [position,position,a,shift_junctions.1],
    by rw [position,position,b,shift_junctions.2.1]⟩

theorem source_position (i : Coordinate) :
    position .enter 0 i=(input.body.frame.position i.1 i.2 : ℝ) := by
  simpa only [position,shift,Pi.add_apply,add_zero] using
    (FiniteContinuation.source_endpoints input input_admissible i).1

theorem target_position (i : Coordinate) :
    position .leave duration i=(generatedBody.frame.position i.1 i.2 : ℝ) := by
  have old := (FiniteContinuation.target_endpoints input input_admissible i).1
  change FiniteContinuation.nuclearPosition input .leave duration i+displacement i=_
  rw [old]
  simp only [generated_position,displacement,Rat.cast_add,Rat.cast_mul]
  rfl

theorem target_momentum (i : Coordinate) :
    momentum .leave duration i=(generatedBody.frame.momentum i.1 i.2 : ℝ) :=
  (FiniteContinuation.target_endpoints input input_admissible i).2.1

theorem position_integral (phase : Phase) (i : Coordinate) :
    position phase duration i-position phase 0 i=∫ t in (0 : ℝ)..duration, velocity phase t i := by
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => position_equation phase t i)
    ((velocity_differentiable phase i).continuous.intervalIntegrable _ _)

theorem total_displacement (i : Coordinate) :
    (∫ t in (0 : ℝ)..duration, velocity .enter t i)+
      (∫ t in (0 : ℝ)..duration, velocity .drive t i)+
      (∫ t in (0 : ℝ)..duration, velocity .leave t i)=displacement i := by
  rw [← position_integral,← position_integral,← position_integral,
    congrFun position_junctions.1 i,congrFun position_junctions.2 i,source_position,target_position]
  simp only [generated_position,Rat.cast_add,Rat.cast_mul,displacement]
  ring

theorem integrated_nonreturning :
    0 < (∫ t in (0 : ℝ)..duration, velocity .enter t (0,0))+
      (∫ t in (0 : ℝ)..duration, velocity .drive t (0,0))+
      (∫ t in (0 : ℝ)..duration, velocity .leave t (0,0)) := by
  rw [total_displacement]
  simpa only [displacement,axisQ,ite_true,Rat.cast_one,mul_one] using
    (Rat.cast_pos.mpr displacement_positive : (0 : ℝ)<(displacementQ : ℝ))

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
