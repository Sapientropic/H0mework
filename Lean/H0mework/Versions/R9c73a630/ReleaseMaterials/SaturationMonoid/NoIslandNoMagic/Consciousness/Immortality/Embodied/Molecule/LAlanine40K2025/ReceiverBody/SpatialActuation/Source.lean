import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Runtime.Consumers

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
open Force.Interface
noncomputable section
abbrev Phase := FiniteContinuation.Phase

def sourceRuntime := SIWork.Runtime.afterFirst
def input := SIWork.Runtime.readCurrent sourceRuntime

theorem input_admissible : FiniteContinuation.Admissible input := sourceRuntime.state.current.2

def totalMassQ : ℚ := ∑ atom : Atom, Reentry.Source.stepReadout.nuclear.masses atom

theorem total_mass_positive : 0 < totalMassQ := by
  apply Finset.sum_pos
  · intro atom _
    exact Inertia.Producer.masses_positive atom
  · exact Finset.univ_nonempty

-- The registered lab direction is fixed; the input stock determines the distance.
def translationRateQ : ℚ := FiniteContinuation.gainQ input/(8*(totalMassQ+1))
def displacementQ : ℚ := Propagation.Producer.nativeClockStep*translationRateQ
def axisQ (axis : Axis) : ℚ := if axis=0 then 1 else 0
def displacement (i : Coordinate) : ℝ := displacementQ*axisQ i.2

theorem translation_rate_positive : 0 < translationRateQ :=
  div_pos (FiniteContinuation.gain_positive input input_admissible) (by linarith [total_mass_positive])

theorem displacement_positive : 0 < displacementQ :=
  mul_pos Propagation.Producer.nativeClockStep_positive translation_rate_positive

def generatedBody : ReceiverBody.Runtime.ActuationResult :=
  { (FiniteContinuation.nextMaterial input).body with
    frame := { (FiniteContinuation.nextMaterial input).body.frame with
      position := fun atom axis => input.body.frame.position atom axis+displacementQ*axisQ axis } }

theorem generated_position (atom : Atom) (axis : Axis) :
    generatedBody.frame.position atom axis=input.body.frame.position atom axis+displacementQ*axisQ axis := rfl

theorem generated_nonreturning : generatedBody.frame.position ≠ input.body.frame.position := by
  intro same
  have coordinate := congrArg (fun position => position 0 0) same
  change input.body.frame.position 0 0+displacementQ*axisQ 0=input.body.frame.position 0 0 at coordinate
  simp only [axisQ,ite_true,mul_one] at coordinate
  linarith only [displacement_positive,coordinate]

theorem generated_internal_difference (a b : Atom) (axis : Axis) :
    generatedBody.frame.position a axis-generatedBody.frame.position b axis=
      input.body.frame.position a axis-input.body.frame.position b axis := by
  rw [generated_position,generated_position]
  ring

theorem generated_kinetic : generatedBody.frame.kinetic=FiniteContinuation.nextKineticQ input := rfl
theorem generated_receiver : generatedBody.resource=(FiniteContinuation.nextMaterial input).body.resource := rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
