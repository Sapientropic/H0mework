import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3IslandStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PlaneMeshStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3VelocityStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ReferenceStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ConstraintStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3EulerStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3DiagnosticsStep

set_option autoImplicit false
namespace FlyCNS.C3Physical
open FlyCNS.C3Actuation

structure Material where
  kinematics : FlyCNS.C3Kinematics.Material
  inertia : FlyCNS.C3Inertia.Material
  collision : FlyCNS.C3PlaneMesh.Material
  island : FlyCNS.C3Island.Material
  velocity : FlyCNS.C3Velocity.Material
  actuation : FlyCNS.C3Actuation.Material
  constraint : FlyCNS.C3Constraint.Material
  euler : FlyCNS.C3Euler.Material
  position : FlyCNS.C3Position.Material
  diagnostics : FlyCNS.C3Diagnostics.Material
  pairFriction : Array Float

structure State where
  position : Array Float
  velocity : Array Float
  warmstart : Array Float
  applied : Array Float
  control : Array Float
  time : Float

structure Current where
  state : State
  pose : FlyCNS.C3Kinematics.Result
  inertia : FlyCNS.C3Inertia.Result
  contacts : Array FlyCNS.C3PlaneMesh.Contact
  island : FlyCNS.C3Island.Result
  velocity : FlyCNS.C3Velocity.Result
  actuation : FlyCNS.C3Actuation.Result
  smooth : FlyCNS.C3Acceleration.Result
  constraint : FlyCNS.C3Constraint.Result
  potential : Float
  kinetic : Float

def contactFrame (m : Material) (inertia : FlyCNS.C3Inertia.Result)
    (contacts : Array FlyCNS.C3PlaneMesh.Contact) : FlyCNS.C3ContactCurrent.Frame := Id.run do
  let mut first := #[];let mut second := #[];let mut positions := #[];let mut frames := #[]
  let mut friction := #[];let mut distances := #[];let mut margins := #[];let mut exclude := #[];let mut pairs := #[]
  for c in contacts do
    first := first.push m.collision.pairFirst[c.pair]!
    second := second.push m.collision.pairSecond[c.pair]!
    positions := positions++c.position
    frames := frames++#[zero,zero,Float.ofBits 0x3FF0000000000000,zero,Float.ofBits 0x3FF0000000000000,zero,
      -(Float.ofBits 0x3FF0000000000000),zero,zero]
    friction := friction++m.pairFriction.extract (5*c.pair) (5*(c.pair+1))
    distances := distances.push c.distance;margins := margins.push m.collision.margin[c.pair]!
    exclude := exclude.push (if c.distance >= m.collision.margin[c.pair]! then 1 else 0)
    pairs := pairs.push c.pair
  return ⟨⟨inertia.center,inertia.motion,first,second,positions,frames,friction,distances,margins,exclude⟩,
    inertia.matrix,pairs⟩

/-- One complete source-owned physical current. Only source state and ROM
enter; every pose, inertia, contact, matrix, force and constraint is generated. -/
def forward (m : Material) (s : State) : Current :=
  let pose := FlyCNS.C3Kinematics.generate m.kinematics s.position
  let inertia := FlyCNS.C3Inertia.fromPose m.inertia pose
  let contacts := FlyCNS.C3PlaneMesh.generate m.collision pose.geomPosition pose.geomRotation
  let island := FlyCNS.C3Island.generate m.island ⟨contactFrame m inertia contacts,s.position⟩
  let current := island.transmission.current
  let transmission := island.transmission
  let motion := FlyCNS.C3Velocity.generate m.velocity ⟨s.position,s.velocity,inertia.motion,inertia.inertia,
    transmission.moments.starts,transmission.moments.counts,transmission.moments.columns,transmission.moments.values⟩
  let (_,reference) := FlyCNS.C3Reference.generate ⟨current.contact.jacobian,s.velocity,
    current.kbip,current.contact.position,current.contact.margin⟩
  let force := FlyCNS.C3Actuation.forces m.actuation ⟨s.control,transmission.lengths,motion.actuatorVelocity,
    transmission.moments.starts,transmission.moments.counts,transmission.moments.columns,transmission.moments.values⟩
  let mm := m.island.transmission.contacts
  let smooth := FlyCNS.C3Acceleration.acceleration ⟨motion.passive,motion.bias,s.applied,force.generalizedForce,
    current.massFactor.factor,current.massFactor.diagonalInverse,mm.massStart,mm.massCount,mm.massColumns⟩
  let mass : FlyCNS.C3Sparse.Matrix := ⟨74,74,inertia.matrix,mm.massStart,mm.massCount,mm.massColumns⟩
  let widths := (List.range current.contact.jacobian.rows).toArray.map fun i => if i%4==0 then 4 else 0
  let constraint := FlyCNS.C3Constraint.advance m.constraint ⟨mass,current.contact.jacobian,current.projection,
    current.massFactor.factor,current.massFactor.diagonalInverse,smooth.force,smooth.acceleration,
    s.warmstart,reference,current.inverse,current.regularizer,widths⟩
  ⟨s,pose,inertia,contacts,island,motion,force,smooth,constraint,
    FlyCNS.C3Diagnostics.potential m.diagnostics s.position pose.inertiaPosition,
    FlyCNS.C3Diagnostics.kinetic m.diagnostics inertia.matrix s.velocity⟩

def integrate (m : Material) (current : Current) : State :=
  let mm := m.island.transmission.contacts
  let euler := FlyCNS.C3Euler.advance m.euler ⟨current.inertia.matrix,mm.massStart,mm.massCount,mm.massColumns,
    current.smooth.force,current.constraint.constraintForce,current.state.velocity,current.state.time⟩
  ⟨FlyCNS.C3Position.advance m.position current.state.position euler.velocity,
    euler.velocity,current.constraint.acceleration,current.state.applied,current.state.control,euler.time⟩

def advance (m : Material) (s : State) : State := integrate m (forward m s)

def reset (m : Material) : State :=
  let r := FlyCNS.C3Diagnostics.reset m.diagnostics
  ⟨r.position,r.velocity,r.warmstart,r.applied,r.control,r.time⟩

/-- The original checks run position then velocity before forward. A bad
acceleration resets and recomputes the same source current before Euler. -/
def step (m : Material) (s : State) : State :=
  let checkedPosition := if (FlyCNS.C3Diagnostics.firstBad s.position).isSome then reset m else s
  let checkedVelocity := if (FlyCNS.C3Diagnostics.firstBad checkedPosition.velocity).isSome then reset m else checkedPosition
  let current := forward m checkedVelocity
  let checkedCurrent := if (FlyCNS.C3Diagnostics.firstBad current.constraint.acceleration).isSome
    then forward m (reset m) else current
  integrate m checkedCurrent

end FlyCNS.C3Physical
