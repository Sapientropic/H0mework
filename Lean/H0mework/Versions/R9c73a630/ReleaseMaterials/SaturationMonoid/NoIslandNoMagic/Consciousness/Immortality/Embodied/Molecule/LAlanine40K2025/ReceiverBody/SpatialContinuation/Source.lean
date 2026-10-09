import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Runtime.Consumers

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation
open Force.Interface
noncomputable section

def sourceRuntime := SpatialActuation.Runtime.afterFirst
def sourceBody := SpatialActuation.Runtime.readCurrent sourceRuntime

structure Material where
  lab : ReceiverBody.Runtime.ActuationResult
  reserve : ℚ

def offset (current : Material) (k : Axis) : ℚ :=
  current.lab.frame.position 0 k-FiniteContinuation.sourceBody.frame.position 0 k

-- Co-moving and lab readers are restrictions of this one current body.
def pullback (current : Material) : FiniteContinuation.Material :=
  { body := { current.lab with
      frame := { current.lab.frame with
        position := fun a k => current.lab.frame.position a k-offset current k } }
    reserve := current.reserve }

def lift (base : FiniteContinuation.Material) (shift : Axis → ℚ) : Material :=
  { lab := { base.body with
      frame := { base.body.frame with
        position := fun a k => base.body.frame.position a k+shift k } }
    reserve := base.reserve }

def Admissible (current : Material) : Prop := FiniteContinuation.Admissible (pullback current)

theorem pullback_origin (current : Material) (k : Axis) :
    (pullback current).body.frame.position 0 k=FiniteContinuation.sourceBody.frame.position 0 k := by
  change current.lab.frame.position 0 k-
    (current.lab.frame.position 0 k-FiniteContinuation.sourceBody.frame.position 0 k)=_
  ring

theorem offset_lift (base : FiniteContinuation.Material) (shift : Axis → ℚ)
    (origin : ∀ k, base.body.frame.position 0 k=FiniteContinuation.sourceBody.frame.position 0 k)
    (k : Axis) : offset (lift base shift) k=shift k := by
  change base.body.frame.position 0 k+shift k-FiniteContinuation.sourceBody.frame.position 0 k=_
  rw [origin k]
  ring

theorem pullback_lift (base : FiniteContinuation.Material) (shift : Axis → ℚ)
    (origin : ∀ k, base.body.frame.position 0 k=FiniteContinuation.sourceBody.frame.position 0 k) :
    pullback (lift base shift)=base := by
  have positions : (fun a k => (lift base shift).lab.frame.position a k-offset (lift base shift) k)=
      base.body.frame.position := by
    funext a k
    rw [offset_lift base shift origin k]
    change base.body.frame.position a k+shift k-shift k=_
    ring
  unfold pullback
  rw [positions]
  rfl

theorem lift_pullback (current : Material) : lift (pullback current) (offset current)=current := by
  have positions : (fun a k => (pullback current).body.frame.position a k+offset current k)=
      current.lab.frame.position := by
    funext a k
    change current.lab.frame.position a k-offset current k+offset current k=_
    ring
  unfold lift
  rw [positions]
  rfl

def initialMaterial : Material :=
  ⟨sourceBody,(FiniteContinuation.nextMaterial SpatialActuation.input).reserve⟩

theorem initial_as_lift : initialMaterial=
    lift (FiniteContinuation.nextMaterial SpatialActuation.input) SpatialActuation.offsetQ := rfl

theorem initial_pullback : pullback initialMaterial=FiniteContinuation.nextMaterial SpatialActuation.input := by
  rw [initial_as_lift]
  apply pullback_lift
  intro k
  exact congrArg (fun p => p 0 k)
    (FiniteContinuation.next_admissible SpatialActuation.input SpatialActuation.input_admissible).position

theorem initial_admissible : Admissible initialMaterial := by
  rw [Admissible,initial_pullback]
  exact FiniteContinuation.next_admissible SpatialActuation.input SpatialActuation.input_admissible

theorem initial_lab : initialMaterial.lab=SpatialActuation.Runtime.readCurrent SpatialActuation.Runtime.afterFirst := rfl

theorem initial_clocks : initialMaterial.lab.resource.quantum.localClock=28*Propagation.Producer.nativeClockStep ∧
    initialMaterial.lab.bodyClock=13*Propagation.Producer.nativeClockStep :=
  SpatialActuation.Runtime.actual_clocks.2

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation
