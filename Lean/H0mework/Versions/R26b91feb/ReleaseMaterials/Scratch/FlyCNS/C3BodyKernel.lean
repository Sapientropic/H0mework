import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PhysicalKernel
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3BodySignalStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ObservationStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ResourceStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3FeedbackStep
set_option autoImplicit false
namespace FlyCNS.C3Body
open FlyCNS.C3Actuation

structure Material where
  physics : FlyCNS.C3Physical.Material
  signal : FlyCNS.C3BodySignal.Material
  observation : FlyCNS.C3Observation.Material
  gait : FlyCNS.C3Gait.Material
  resource : FlyCNS.C3Resource.Material
  feedback : FlyCNS.C3Feedback.Material
  legActuators : Array Nat
  mouthActuators : Array Nat
  adhesionActuators : Array Nat
  neutral : Array Float
  mouthPitch : Float
  mouthBody : Nat
  headGeom : Nat
  antennalGeoms : Array Nat

structure State where
  physics : FlyCNS.C3Physical.State
  signal : FlyCNS.C3BodySignal.State
  gait : FlyCNS.C3Gait.State
  resource : FlyCNS.C3Resource.State
  odorGains : Array Float

structure Result where
  state : State
  feedback : FlyCNS.C3Feedback.Result
  physical : Array FlyCNS.C3Physical.Current
  controls : Array (Array Float)
  receipts : Array Float

def control (m : Material) (current : FlyCNS.C3Physical.Current)
    (gait : FlyCNS.C3Gait.Result) (feeding : Float) (enabled : Bool) : Array Float := Id.run do
  let angles := if enabled then gait.jointAngles else m.neutral
  let adhesion := if enabled then gait.adhesion else Array.replicate 6 true
  let mut result := current.state.control
  for i in [:m.legActuators.size] do result := result.set! m.legActuators[i]! angles[i]!
  for i in [:m.adhesionActuators.size] do
    result := result.set! m.adhesionActuators[i]! (if adhesion[i]! then Float.ofBits 0x3FF0000000000000 else zero)
  for i in [:m.mouthActuators.size] do
    result := result.set! m.mouthActuators[i]! (((if i==0 then Float.ofBits 0x3FF0000000000000 else -(Float.ofBits 0x3FF0000000000000))*feeding)*m.mouthPitch)
  return result

def observation (m : Material) (current : FlyCNS.C3Physical.Current) : FlyCNS.C3Observation.Result :=
  let contact := FlyCNS.C3Physical.contactFrame m.physics current.inertia current.contacts
  let addresses := current.island.transmission.current.contact.contactAddress.map Int64.ofInt
  FlyCNS.C3Observation.generate m.observation ⟨current.pose.position,current.pose.rotation,
    contact.contact.geomFirst,contact.contact.geomSecond,contact.contact.exclude,addresses,
    contact.contact.friction,contact.contact.frames,current.constraint.contactForce⟩

/-- Original one neural-tick body law: actual spikes generate signal, then
ten self-produced physical/world updates generate the next full afferents. -/
def advance (m : Material) (s : State) (fired : Array Nat) : Result := Id.run do
  let signal := FlyCNS.C3BodySignal.receive m.signal s.signal fired
  let mut physical := FlyCNS.C3Physical.forward m.physics s.physics
  let mut gait := s.gait
  let mut world := s.resource
  let mut taste := #[zero,zero]
  let mut sugar := zero;let mut water := zero
  let mut trace := #[];let mut controls := #[]
  for _ in [:10] do
    let previous := physical.pose.position.extract (3*m.observation.thorax) (3*m.observation.thorax+3)
    let obs := observation m physical
    let walking := FlyCNS.C3Gait.advance m.gait gait signal.signal obs.observation
    if signal.state.controllerEnabled then gait := walking.state
    let ctrl := control m physical walking signal.feeding signal.state.controllerEnabled
    controls := controls.push ctrl
    let updated : FlyCNS.C3Physical.State := {physical.state with control:=ctrl}
    let before := FlyCNS.C3Physical.forward m.physics updated
    let next := FlyCNS.C3Physical.integrate m.physics before
    physical := FlyCNS.C3Physical.forward m.physics next
    let body : FlyCNS.C3Resource.BodyFrame := ⟨physical.pose.position.extract (3*m.mouthBody) (3*m.mouthBody+3),
      previous,physical.pose.position.extract (3*m.observation.thorax) (3*m.observation.thorax+3),
      physical.actuation.actuatorForce,physical.velocity.actuatorVelocity,signal.feeding⟩
    let resource := FlyCNS.C3Resource.advance m.resource world body
    world := resource.state;taste := taste.mapIdx fun i v => v+resource.taste[i]!
    sugar := sugar+resource.sugar;water := water+resource.water
    trace := trace.push physical
  let ports := m.antennalGeoms++#[m.headGeom]
  let points := ports.flatMap fun i => physical.pose.geomPosition.extract (3*i) (3*i+3)
  let fraction := Float.ofBits 0x4024000000000000
  let feedback := FlyCNS.C3Feedback.generate m.feedback ⟨points,s.odorGains,taste.map (·/fraction),world.peptide,#[sugar,water]⟩
  return ⟨⟨physical.state,signal.state,gait,world,s.odorGains⟩,feedback,trace,controls,#[sugar,water]⟩
end FlyCNS.C3Body
