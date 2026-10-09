import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation.Step

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation
noncomputable section
abbrev Phase := FiniteContinuation.Phase

def shift (current : Material) : Phase → ℝ → Configuration
  | .enter => fun _ i => offset current i.2
  | .drive => fun t i => (offset current i.2 : ℝ)+(increment current i.2 : ℝ)*FiniteActuation.progress t
  | .leave => fun _ i => (offset current i.2 : ℝ)+(increment current i.2 : ℝ)

def shiftRate (current : Material) : Phase → ℝ → Configuration
  | .enter => fun _ _ => 0
  | .drive => fun t i => (increment current i.2 : ℝ)*FiniteActuation.progressRate t
  | .leave => fun _ _ => 0

def position (current : Material) (phase : Phase) (t : ℝ) : Configuration :=
  FiniteContinuation.nuclearPosition (pullback current) phase t+shift current phase t

def velocity (current : Material) (phase : Phase) (t : ℝ) : Configuration :=
  FiniteContinuation.velocity (pullback current) phase t+shiftRate current phase t

def momentum (current : Material) (phase : Phase) (t : ℝ) : Configuration :=
  FiniteContinuation.nuclearMomentum (pullback current) phase t

def force (current : Material) (phase : Phase) (t : ℝ) : Configuration :=
  FiniteContinuation.nuclearForce (pullback current) phase t

def receiver (current : Material) (phase : Phase) (t : ℝ) : ℝ :=
  FiniteContinuation.receiver (pullback current) phase t
def receiverForce (current : Material) (phase : Phase) (t : ℝ) : ℝ :=
  FiniteContinuation.receiverForce (pullback current) phase t

theorem shift_derivative (current : Material) (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => shift current phase time i) (shiftRate current phase t i) t := by
  cases phase with
  | enter => exact hasDerivAt_const t _
  | drive => exact ((FiniteActuation.progress_derivative t).const_mul (increment current i.2 : ℝ)).const_add _
  | leave => exact hasDerivAt_const t _

theorem position_equation (current : Material) (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => position current phase time i) (velocity current phase t i) t :=
  (FiniteContinuation.position_equation (pullback current) phase t i).add (shift_derivative current phase t i)

theorem momentum_equation (current : Material) (phase : Phase) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => momentum current phase time i) (force current phase t i) t :=
  FiniteContinuation.momentum_equation (pullback current) phase t i

theorem receiver_equation (current : Material) (phase : Phase) (t : ℝ) :
    HasDerivAt (receiver current phase) (receiverForce current phase t) t :=
  FiniteContinuation.receiver_equation (pullback current) phase t

theorem velocity_differentiable (current : Material) (phase : Phase) (i : Coordinate) :
    Differentiable ℝ (fun t => velocity current phase t i) := by
  unfold velocity FiniteContinuation.velocity shiftRate
  cases phase <;> dsimp only [Pi.add_apply,FiniteActuation.onRate,FiniteActuation.offRate,
    FiniteActuation.rampMomentum,FiniteActuation.onTime,FiniteActuation.offTime,
    FiniteActuation.progressRate] <;> fun_prop

theorem force_differentiable (current : Material) (phase : Phase) (i : Coordinate) :
    Differentiable ℝ (fun t => force current phase t i) := by
  unfold force FiniteContinuation.nuclearForce
  cases phase <;> dsimp only [FiniteActuation.onRate,FiniteActuation.offRate,
    FiniteContinuation.pulseForce,FiniteActuation.progressRate] <;> fun_prop

theorem shift_junctions (current : Material) :
    shift current .enter duration=shift current .drive 0 ∧ shift current .drive duration=shift current .leave 0 ∧
    shiftRate current .enter duration=shiftRate current .drive 0 ∧ shiftRate current .drive duration=shiftRate current .leave 0 := by
  simp only [shift,shiftRate,FiniteActuation.progress_endpoints.1,
    FiniteActuation.progress_endpoints.2,FiniteActuation.progress_rate_endpoints.1,
    FiniteActuation.progress_rate_endpoints.2,mul_zero,mul_one,add_zero]
  trivial

theorem position_junctions (current : Material) :
    position current .enter duration=position current .drive 0 ∧
    position current .drive duration=position current .leave 0 := by
  rcases FiniteContinuation.state_junctions (pullback current) with ⟨a,b,_⟩
  exact ⟨by rw [position,position,a,(shift_junctions current).1],
    by rw [position,position,b,(shift_junctions current).2.1]⟩

theorem source_position (current : Material) (valid : Admissible current) (i : Coordinate) :
    position current .enter 0 i=(current.lab.frame.position i.1 i.2 : ℝ) := by
  have old := (FiniteContinuation.source_endpoints (pullback current) valid i).1
  change FiniteContinuation.nuclearPosition (pullback current) .enter 0 i+(offset current i.2 : ℝ)=_
  rw [old]
  change ((current.lab.frame.position i.1 i.2-offset current i.2 : ℚ) : ℝ)+(offset current i.2 : ℝ)=_
  push_cast
  ring

theorem target_position (current : Material) (valid : Admissible current) (i : Coordinate) :
    position current .leave duration i=((nextMaterial current).lab.frame.position i.1 i.2 : ℝ) := by
  have old := (FiniteContinuation.target_endpoints (pullback current) valid i).1
  change FiniteContinuation.nuclearPosition (pullback current) .leave duration i+
    ((offset current i.2 : ℝ)+(increment current i.2 : ℝ))=_
  rw [old,next_position]
  change ((current.lab.frame.position i.1 i.2-offset current i.2 : ℚ) : ℝ)+
    ((offset current i.2 : ℝ)+(increment current i.2 : ℝ))=
      ((current.lab.frame.position i.1 i.2+increment current i.2 : ℚ) : ℝ)
  push_cast
  ring

theorem target_momentum (current : Material) (valid : Admissible current) (i : Coordinate) :
    momentum current .leave duration i=((nextMaterial current).lab.frame.momentum i.1 i.2 : ℝ) :=
  (FiniteContinuation.target_endpoints (pullback current) valid i).2.1

theorem position_integral (current : Material) (phase : Phase) (i : Coordinate) :
    position current phase duration i-position current phase 0 i=
      ∫ t in (0 : ℝ)..duration, velocity current phase t i :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => position_equation current phase t i)
    ((velocity_differentiable current phase i).continuous.intervalIntegrable _ _)).symm

theorem total_displacement (current : Material) (valid : Admissible current) (i : Coordinate) :
    (∫ t in (0 : ℝ)..duration, velocity current .enter t i)+
      (∫ t in (0 : ℝ)..duration, velocity current .drive t i)+
      (∫ t in (0 : ℝ)..duration, velocity current .leave t i)=(increment current i.2 : ℝ) := by
  rw [← position_integral,← position_integral,← position_integral,
    congrFun (position_junctions current).1 i,congrFun (position_junctions current).2 i,
    source_position current valid,target_position current valid,next_position]
  push_cast
  ring

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation
