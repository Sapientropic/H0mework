import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime.Consumers

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
open Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
noncomputable section

-- One actual generated current, including its already-debited receiver.
def sourceRuntime := FiniteActuation.Runtime.afterFirst
def sourceBody := FiniteActuation.Runtime.readCurrent sourceRuntime

theorem source_body_generated : sourceBody=FiniteActuation.generatedBody := rfl

structure Material where
  body : ReceiverBody.Runtime.ActuationResult
  reserve : ℚ

def momentum (current : Material) (i : Coordinate) : ℝ := current.body.frame.momentum i.1 i.2

def gainQ (current : Material) : ℚ :=
  current.reserve/(8*(current.body.frame.kinetic+current.reserve+1))

def nextKineticQ (current : Material) : ℚ := (1+gainQ current)^2*current.body.frame.kinetic

def nextFrame (current : Material) : Inertia.Interface.NuclearFrame :=
  { current.body.frame with
    momentum := fun atom axis => (1+gainQ current)*current.body.frame.momentum atom axis
    kinetic := nextKineticQ current
    total := nextKineticQ current+current.body.frame.potential }

def nextMaterial (current : Material) : Material :=
  { body :=
      { current.body with
        resource := ⟨Live.loadNext (Live.loadNext (Live.loadNext current.body.resource.quantum)),
          current.body.resource.momentum+(current.body.frame.kinetic : ℝ)-(nextKineticQ current : ℝ)⟩
        frame := nextFrame current
        bodyClock := current.body.bodyClock+3*Propagation.Producer.nativeClockStep }
    reserve := current.reserve/2 }

structure Admissible (current : Material) : Prop where
  positiveReserve : 0 < current.reserve
  reserveBelowStock : (current.reserve : ℝ) < current.body.resource.momentum
  positiveKinetic : 0 < current.body.frame.kinetic
  kinetic : nuclearKinetic (momentum current)=(current.body.frame.kinetic : ℝ)
  total : current.body.frame.total=current.body.frame.kinetic+current.body.frame.potential
  position : current.body.frame.position=sourceBody.frame.position
  force : current.body.frame.force=sourceBody.frame.force
  potential : current.body.frame.potential=sourceBody.frame.potential
  held : current.body.held=sourceBody.held
  realized : current.body.realized=sourceBody.realized
  inheritedResidual : current.body.inheritedResidual=sourceBody.inheritedResidual
  newNumericalResidual : current.body.newNumericalResidual=sourceBody.newNumericalResidual

def initialMaterial : Material := ⟨sourceBody,FiniteActuation.reserveFloorQ/2⟩

theorem initial_admissible : Admissible initialMaterial := by
  have floorPositive : 0 < FiniteActuation.reserveFloorQ :=
    Rat.cast_pos.mp FiniteActuation.reserve_floor_positive
  have kineticPositive : 0 < nuclearKinetic (FiniteActuation.plateauMomentum 1) := by
    linarith only [FiniteActuation.initial_kinetic_positive,FiniteActuation.target_debit_positive_and_bounded.1]
  refine
    { positiveReserve := half_pos floorPositive
      reserveBelowStock := ?_
      positiveKinetic := ?_
      kinetic := FiniteActuation.target_kinetic_generated
      total := rfl
      position := rfl
      force := rfl
      potential := rfl
      held := rfl
      realized := rfl
      inheritedResidual := rfl
      newNumericalResidual := rfl }
  · change ((FiniteActuation.reserveFloorQ/2 : ℚ) : ℝ) < FiniteActuation.generatedBody.resource.momentum
    push_cast
    have floor := FiniteActuation.reserve_floor_current
    change (FiniteActuation.reserveFloorQ : ℝ)<FiniteActuation.initialReceiver at floor
    linarith only [floor,FiniteActuation.target_stock]
  · have positive : (0 : ℝ) < (FiniteActuation.nextKineticQ : ℝ) := by
      rw [FiniteActuation.target_kinetic]
      exact kineticPositive
    exact Rat.cast_pos.mp positive

theorem initial_clocks : initialMaterial.body.resource.quantum.localClock=22*Propagation.Producer.nativeClockStep ∧
    initialMaterial.body.bodyClock=7*Propagation.Producer.nativeClockStep := FiniteActuation.generated_clocks

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
