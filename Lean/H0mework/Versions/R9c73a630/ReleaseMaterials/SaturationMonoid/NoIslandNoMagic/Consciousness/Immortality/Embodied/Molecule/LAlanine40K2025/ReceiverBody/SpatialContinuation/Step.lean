import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation.Source

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation
open Force.Interface
noncomputable section

def displacementQ (current : Material) : ℚ :=
  Propagation.Producer.nativeClockStep*FiniteContinuation.gainQ (pullback current)/
    (8*(SpatialActuation.totalMassQ+1))

def increment (current : Material) (k : Axis) : ℚ := displacementQ current*SpatialActuation.axisQ k

def nextMaterial (current : Material) : Material :=
  lift (FiniteContinuation.nextMaterial (pullback current)) (fun k => offset current k+increment current k)

theorem pullback_next (current : Material) :
    pullback (nextMaterial current)=FiniteContinuation.nextMaterial (pullback current) := by
  unfold nextMaterial
  apply pullback_lift
  exact pullback_origin current

theorem next_admissible (current : Material) (valid : Admissible current) : Admissible (nextMaterial current) := by
  rw [Admissible,pullback_next]
  exact FiniteContinuation.next_admissible (pullback current) valid

theorem displacement_positive (current : Material) (valid : Admissible current) : 0 < displacementQ current :=
  div_pos (mul_pos Propagation.Producer.nativeClockStep_positive
    (FiniteContinuation.gain_positive (pullback current) valid)) (by linarith [SpatialActuation.total_mass_positive])

theorem next_position (current : Material) (a : Atom) (k : Axis) :
    (nextMaterial current).lab.frame.position a k=current.lab.frame.position a k+increment current k := by
  change current.lab.frame.position a k-offset current k+(offset current k+increment current k)=_
  ring

theorem next_offset (current : Material) (k : Axis) :
    offset (nextMaterial current) k=offset current k+increment current k :=
  offset_lift (FiniteContinuation.nextMaterial (pullback current)) _ (pullback_origin current) k

theorem next_nonreturning (current : Material) (valid : Admissible current) :
    (nextMaterial current).lab.frame.position≠current.lab.frame.position := by
  intro same
  have coordinate := congrArg (fun p => p 0 0) same
  rw [next_position] at coordinate
  simp only [increment,SpatialActuation.axisQ,ite_true,mul_one] at coordinate
  linarith only [displacement_positive current valid,coordinate]

theorem next_relative_geometry (current : Material) (a b : Atom) (k : Axis) :
    (nextMaterial current).lab.frame.position a k-(nextMaterial current).lab.frame.position b k=
      current.lab.frame.position a k-current.lab.frame.position b k := by
  rw [next_position,next_position]
  ring

theorem next_reserve (current : Material) : (nextMaterial current).reserve=current.reserve/2 := rfl

theorem next_positive_reserve (current : Material) (valid : Admissible current) :
    0 < (nextMaterial current).reserve ∧ ((nextMaterial current).reserve : ℝ)<(nextMaterial current).lab.resource.momentum :=
  FiniteContinuation.next_reserve (pullback current) valid

theorem next_positive_stock (current : Material) (valid : Admissible current) :
    0 < (nextMaterial current).lab.resource.momentum :=
  (half_pos (FiniteContinuation.stock_positive (pullback current) valid)).trans
    (FiniteContinuation.next_stock (pullback current) valid)

theorem next_whole_account (current : Material) (valid : Admissible current) :
    SpatialActuation.wholeBodyAccount (nextMaterial current).lab=SpatialActuation.wholeBodyAccount current.lab :=
  FiniteContinuation.next_whole_account (pullback current) valid

theorem next_clocks (current : Material) :
    (nextMaterial current).lab.resource.quantum.localClock=current.lab.resource.quantum.localClock+3*Propagation.Producer.nativeClockStep ∧
    (nextMaterial current).lab.bodyClock=current.lab.bodyClock+3*Propagation.Producer.nativeClockStep :=
  FiniteContinuation.next_clocks (pullback current)

theorem first_clocks :
    (nextMaterial initialMaterial).lab.resource.quantum.localClock=31*Propagation.Producer.nativeClockStep ∧
    (nextMaterial initialMaterial).lab.bodyClock=16*Propagation.Producer.nativeClockStep := by
  have generated := next_clocks initialMaterial
  rw [initial_clocks.1,initial_clocks.2] at generated
  constructor <;> linarith only [generated.1,generated.2]

def unreserved (current : Material) : ℝ := current.lab.resource.momentum-(current.reserve : ℝ)

theorem next_unreserved_increases (current : Material) (valid : Admissible current) :
    unreserved current<unreserved (nextMaterial current) :=
  FiniteContinuation.next_unreserved_increases (pullback current) valid

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation
