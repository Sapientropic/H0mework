import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3InertiaStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3SparseStep

/-! Original current-dependent COM velocity, passive force and abbreviated RNE.
No body velocity, bias force or physics-after is a parameter. -/
set_option autoImplicit false
namespace FlyCNS.C3Velocity
open FlyCNS.C3Actuation FlyCNS.C3Kinematics

structure Material where
  parent : Array Nat
  bodyDofStart : Array Nat
  bodyDofCount : Array Nat
  dofJoint : Array Nat
  dofBody : Array Nat
  jointType : Array Nat
  jointPosition : Array Nat
  jointDof : Array Nat
  stiffness : Array Float
  springPosition : Array Float
  damping : Array Float
  gravity : Array Float

structure Frame where
  position : Array Float
  velocity : Array Float
  motion : Array Float
  inertia : Array Float
  momentStart : Array Nat
  momentCount : Array Nat
  momentColumns : Array Nat
  moment : Array Float

structure Result where
  bodyVelocity : Array Float
  motionDerivative : Array Float
  spring : Array Float
  damper : Array Float
  passive : Array Float
  bias : Array Float
  actuatorVelocity : Array Float
  acceleration : Array Float
  bodyForce : Array Float

def add6 (a b : Array Float) : Array Float := (List.range 6).toArray.map fun i => a[i]!+b[i]!

def dofProduct (motion velocity : Array Float) (start count : Nat) : Array Float := Id.run do
  if count == 1 then return (part motion 6 start).map fun x => x*velocity[start]!
  let mut result := Array.replicate 6 zero
  for j in [start:start+count] do
    if velocity[j]! != zero then
      for k in [:6] do result := result.set! k (fused motion[6*j+k]! velocity[j]! result[k]!)
  return result

def crossMotion (v a : Array Float) : Array Float :=
  #[fused (-v[2]!) a[1]! (v[1]!*a[2]!),
    fused v[2]! a[0]! ((-v[0]!)*a[2]!),
    fused (-v[1]!) a[0]! (v[0]!*a[1]!),
    (fused (-v[2]!) a[4]! (v[1]!*a[5]!))+(fused (-v[5]!) a[1]! (v[4]!*a[2]!)),
    (fused v[2]! a[3]! ((-v[0]!)*a[5]!))+(fused v[5]! a[0]! ((-v[3]!)*a[2]!)),
    (fused (-v[1]!) a[3]! (v[0]!*a[4]!))+(fused (-v[4]!) a[0]! (v[3]!*a[1]!))]

def crossForce (v f : Array Float) : Array Float :=
  #[(fused (-v[2]!) f[1]! (v[1]!*f[2]!))+(fused (-v[5]!) f[4]! (v[4]!*f[5]!)),
    (fused v[2]! f[0]! ((-v[0]!)*f[2]!))+(fused v[5]! f[3]! ((-v[3]!)*f[5]!)),
    (fused (-v[1]!) f[0]! (v[0]!*f[1]!))+(fused (-v[4]!) f[3]! (v[3]!*f[4]!)),
    fused (-v[2]!) f[4]! (v[1]!*f[5]!),
    fused v[2]! f[3]! ((-v[0]!)*f[5]!),
    fused (-v[1]!) f[3]! (v[0]!*f[4]!)]

def generate (m : Material) (frame : Frame) : Result := Id.run do
  let n := m.parent.size
  let nv := frame.velocity.size
  let mut bodyVelocity := Array.replicate (6*n) zero
  let mut derivative := Array.replicate (6*nv) zero
  for i in [1:n] do
    let start := m.bodyDofStart[i]!
    let count := m.bodyDofCount[i]!
    let mut v := part bodyVelocity 6 m.parent[i]!
    let mut j := 0
    while j < count do
      let dof := start+j
      if m.jointType[m.dofJoint[dof]!]! == 0 then
        v := add6 v (dofProduct frame.motion frame.velocity dof 3)
        j := j+3
        for k in [:3] do derivative := put derivative 6 (start+j+k) (crossMotion v (part frame.motion 6 (start+j+k)))
        v := add6 v (dofProduct frame.motion frame.velocity (start+j) 3)
        j := j+3
      else
        derivative := put derivative 6 dof (crossMotion v (part frame.motion 6 dof))
        v := add6 v (dofProduct frame.motion frame.velocity dof 1)
        j := j+1
    bodyVelocity := put bodyVelocity 6 i v
  let mut spring := Array.replicate nv zero
  for j in [:m.jointType.size] do
    if m.stiffness[j]! != zero then
      let address := m.jointPosition[j]!
      spring := spring.set! m.jointDof[j]! (-(frame.position[address]!-m.springPosition[address]!)*m.stiffness[j]!)
  let damper := (List.range nv).toArray.map fun i => if m.damping[i]! == zero then zero else (-frame.velocity[i]!)*(m.damping[i]!+zero)
  let passive := (List.range nv).toArray.map fun i => spring[i]!+damper[i]!
  let mut acc := put (Array.replicate (6*n) zero) 6 0 (#[zero,zero,zero] ++ m.gravity.map fun x => -x)
  let mut force := Array.replicate (6*n) zero
  for i in [1:n] do
    let v := add6 (part acc 6 m.parent[i]!) (dofProduct derivative frame.velocity m.bodyDofStart[i]! m.bodyDofCount[i]!)
    acc := put acc 6 i v
    let inertia := part frame.inertia 10 i
    let velocity := part bodyVelocity 6 i
    let f := add6 (FlyCNS.C3Inertia.multiply inertia v)
      (crossForce velocity (FlyCNS.C3Inertia.multiply inertia velocity))
    force := put force 6 i f
  for back in [:n-1] do
    let i := n-back-1
    let parent := m.parent[i]!
    if parent != 0 then force := put force 6 parent (add6 (part force 6 parent) (part force 6 i))
  let bias := (List.range nv).toArray.map fun i => FlyCNS.C3Inertia.dot6 (part frame.motion 6 i) (part force 6 m.dofBody[i]!)
  let actuatorVelocity := (List.range frame.momentStart.size).toArray.map fun i =>
    FlyCNS.C3Sparse.dotIndexed frame.moment frame.velocity frame.momentColumns frame.momentStart[i]! frame.momentCount[i]!
  return ⟨bodyVelocity,derivative,spring,damper,passive,bias,actuatorVelocity,acc,force⟩
end FlyCNS.C3Velocity
