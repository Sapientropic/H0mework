import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3SincosROM

set_option autoImplicit false
namespace FlyCNS.C3Position
open FlyCNS.C3Actuation
def one : Float := Float.ofBits 0x3FF0000000000000
def minimum : Float := Float.ofBits 0x3CD203AF9EE75616

structure Material where
  timestep : Float
  jointTypes : Array Nat
  positionAddress : Array Nat
  velocityAddress : Array Nat

def norm3 (v : Array Float) : Float :=
  (fused v[2]! v[2]! (fused v[0]! v[0]! (v[1]!*v[1]!))).sqrt
def norm4 (v : Array Float) : Float :=
  (fused v[3]! v[3]! (fused v[2]! v[2]! (fused v[0]! v[0]! (v[1]!*v[1]!)))).sqrt

def normalize4 (q : Array Float) : Array Float :=
  let n := norm4 q
  if n < minimum then #[one,zero,zero,zero]
  else if (n-one).abs > minimum then q.map fun v => v*(one/n) else q

def product (a b : Array Float) : Array Float :=
  #[fused (-a[3]!) b[3]! (fused (-a[2]!) b[2]! (fused a[0]! b[0]! (-a[1]!*b[1]!))),
    fused (-a[3]!) b[2]! (fused a[2]! b[3]! (fused a[0]! b[1]! (a[1]!*b[0]!))),
    fused a[3]! b[1]! (fused a[2]! b[0]! (fused a[0]! b[2]! (-a[1]!*b[3]!))),
    fused a[3]! b[0]! (fused (-a[2]!) b[1]! (fused a[0]! b[3]! (a[1]!*b[2]!)))]

def quaternion (q v : Array Float) (dt : Float) : Array Float :=
  let n := norm3 v
  let axis := if n < minimum then #[one,zero,zero] else v.map fun value => value*(one/n)
  let angle := dt*n
  let halfAngle := (Float.ofBits 0x3FE0000000000000)*angle
  let rotation := if angle == zero then #[one,zero,zero,zero] else
    let s := FlyCNS.C3Sincos.sine halfAngle
    #[FlyCNS.C3Sincos.cosine halfAngle,axis[0]!*s,axis[1]!*s,axis[2]!*s]
  product (normalize4 q) rotation

def advance (m : Material) (before velocity : Array Float) : Array Float := Id.run do
  let mut position := before
  for j in [:m.jointTypes.size] do
    let p := m.positionAddress[j]!
    let v := m.velocityAddress[j]!
    if m.jointTypes[j]! == 0 then
      for k in [:3] do position := position.set! (p+k) (fused m.timestep velocity[v+k]! position[p+k]!)
      let q := quaternion (position.extract (p+3) (p+7)) (velocity.extract (v+3) (v+6)) m.timestep
      for k in [:4] do position := position.set! (p+3+k) q[k]!
    else if m.jointTypes[j]! == 1 then
      let q := quaternion (position.extract p (p+4)) (velocity.extract v (v+3)) m.timestep
      for k in [:4] do position := position.set! (p+k) q[k]!
    else position := position.set! p (fused m.timestep velocity[v]! position[p]!)
  return position

end FlyCNS.C3Position
