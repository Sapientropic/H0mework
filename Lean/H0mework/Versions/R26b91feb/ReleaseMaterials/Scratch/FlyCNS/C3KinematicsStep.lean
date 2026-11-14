import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PositionStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PairedSincosStep

/-! Original C7 kinematics1/2. Only source ROM and present qpos are inputs;
all Cartesian bodies, inertias, joint ports, geoms and sites are generated. -/
set_option autoImplicit false
namespace FlyCNS.C3Kinematics
open FlyCNS.C3Actuation FlyCNS.C3Position

structure Material where
  parent : Array Nat
  jointStart : Array Nat
  jointCount : Array Nat
  bodyPosition : Array Float
  bodyQuaternion : Array Float
  inertiaPosition : Array Float
  inertiaQuaternion : Array Float
  bodyFrame : Array Nat
  jointType : Array Nat
  jointAddress : Array Nat
  jointPosition : Array Float
  jointAxis : Array Float
  initialPosition : Array Float
  geomBody : Array Nat
  geomPosition : Array Float
  geomQuaternion : Array Float
  geomFrame : Array Nat
  siteBody : Array Nat
  sitePosition : Array Float
  siteQuaternion : Array Float
  siteFrame : Array Nat

structure Result where
  position : Array Float
  quaternion : Array Float
  rotation : Array Float
  anchor : Array Float
  axis : Array Float
  inertiaPosition : Array Float
  inertiaRotation : Array Float
  geomPosition : Array Float
  geomRotation : Array Float
  sitePosition : Array Float
  siteRotation : Array Float
  deriving Inhabited

def identity : Array Float := #[one,zero,zero,zero,one,zero,zero,zero,one]
def unit : Array Float := #[one,zero,zero,zero]
def part (a : Array Float) (width i : Nat) : Array Float := a.extract (width*i) (width*(i+1))
def put (a : Array Float) (width i : Nat) (v : Array Float) : Array Float := Id.run do
  let mut result := a
  for k in [:width] do result := result.set! (width*i+k) v[k]!
  return result
def add3 (a b : Array Float) : Array Float := #[a[0]!+b[0]!,a[1]!+b[1]!,a[2]!+b[2]!]
def subtract3 (a b : Array Float) : Array Float := #[a[0]!-b[0]!,a[1]!-b[1]!,a[2]!-b[2]!]

def matrixVector (m v : Array Float) : Array Float :=
  (List.range 3).toArray.map fun i => fused m[3*i+2]! v[2]! (fused m[3*i]! v[0]! (m[3*i+1]!*v[1]!))

def rotate (v q : Array Float) : Array Float :=
  if q[0]! == one && q[1]! == zero && q[2]! == zero && q[3]! == zero then v else
  let t0 := fused (-q[3]!) v[1]! (fused q[0]! v[0]! (q[2]!*v[2]!))
  let t1 := fused (-q[1]!) v[2]! (fused q[0]! v[1]! (q[3]!*v[0]!))
  let t2 := fused (-q[2]!) v[0]! (fused q[0]! v[2]! (q[1]!*v[1]!))
  let two := Float.ofBits 0x4000000000000000
  #[fused two (fused q[2]! t2 ((-q[3]!)*t1)) v[0]!,
    fused two (fused q[3]! t0 ((-q[1]!)*t2)) v[1]!,
    fused two (fused q[1]! t1 ((-q[2]!)*t0)) v[2]!]

def matrix (q : Array Float) : Array Float :=
  if q[0]! == one && q[1]! == zero && q[2]! == zero && q[3]! == zero then identity else
  let q00 := q[0]!*q[0]!; let q01 := q[0]!*q[1]!; let q02 := q[0]!*q[2]!; let q03 := q[0]!*q[3]!
  let q11 := q[1]!*q[1]!; let q12 := q[1]!*q[2]!; let q13 := q[1]!*q[3]!
  let q22 := q[2]!*q[2]!; let q23 := q[2]!*q[3]!; let q33 := q[3]!*q[3]!
  let twice := fun x : Float => x+x
  #[((q00+q11)-q22)-q33,twice (q12-q03),twice (q13+q02),
    twice (q12+q03),((q00-q11)+q22)-q33,twice (q23-q01),
    twice (q13-q02),twice (q23+q01),((q00-q11)-q22)+q33]

def axisAngle (axis : Array Float) (angle : Float) : Array Float :=
  if angle == zero then unit else
  let halfAngle := angle*(Float.ofBits 0x3FE0000000000000)
  let (s,c) := FlyCNS.C3PairedSincos.evaluate halfAngle
  #[c,axis[0]!*s,axis[1]!*s,axis[2]!*s]

def localPose (r : Result) (body frame : Nat) (pos quat : Array Float) : Array Float × Array Float :=
  let position := if frame == 1 then part r.position 3 body
    else if frame == 2 then part r.inertiaPosition 3 body
    else add3 (matrixVector (part r.rotation 9 body) pos) (part r.position 3 body)
  let rotation := if frame == 1 || frame == 3 then part r.rotation 9 body
    else if frame == 2 || frame == 4 then part r.inertiaRotation 9 body
    else matrix (product (part r.quaternion 4 body) quat)
  (position,rotation)

def generate (m : Material) (qpos : Array Float) : Result := Id.run do
  let n := m.parent.size
  let mut r : Result := ⟨Array.replicate (3*n) zero,put (Array.replicate (4*n) zero) 4 0 unit,
    put (Array.replicate (9*n) zero) 9 0 identity,Array.replicate (3*m.jointType.size) zero,
    Array.replicate (3*m.jointType.size) zero,Array.replicate (3*n) zero,
    put (Array.replicate (9*n) zero) 9 0 identity,Array.replicate (3*m.geomBody.size) zero,
    Array.replicate (9*m.geomBody.size) zero,Array.replicate (3*m.siteBody.size) zero,
    Array.replicate (9*m.siteBody.size) zero⟩
  for i in [1:n] do
    let start := m.jointStart[i]!
    let count := m.jointCount[i]!
    let mut pos := part m.bodyPosition 3 i
    let mut quat := part m.bodyQuaternion 4 i
    if count == 1 && m.jointType[start]! == 0 then
      let address := m.jointAddress[start]!
      pos := qpos.extract address (address+3)
      quat := normalize4 (qpos.extract (address+3) (address+7))
      r := {r with anchor := put r.anchor 3 start pos,axis := put r.axis 3 start (part m.jointAxis 3 start)}
    else
      let parent := m.parent[i]!
      if parent != 0 then
        pos := add3 (matrixVector (part r.rotation 9 parent) pos) (part r.position 3 parent)
        quat := product (part r.quaternion 4 parent) quat
      for j in [start:start+count] do
        let address := m.jointAddress[j]!
        let axis := rotate (part m.jointAxis 3 j) quat
        let anchor := add3 (rotate (part m.jointPosition 3 j) quat) pos
        quat := product quat (axisAngle (part m.jointAxis 3 j) (qpos[address]!-m.initialPosition[address]!))
        pos := subtract3 anchor (rotate (part m.jointPosition 3 j) quat)
        r := {r with anchor := put r.anchor 3 j anchor,axis := put r.axis 3 j axis}
    quat := normalize4 quat
    r := {r with position := put r.position 3 i pos,quaternion := put r.quaternion 4 i quat, rotation := put r.rotation 9 i (matrix quat)}
  for i in [1:n] do
    let (pos,rot) := localPose r i m.bodyFrame[i]! (part m.inertiaPosition 3 i) (part m.inertiaQuaternion 4 i)
    r := {r with inertiaPosition := put r.inertiaPosition 3 i pos,inertiaRotation := put r.inertiaRotation 9 i rot}
  for i in [:m.geomBody.size] do
    let (pos,rot) := localPose r m.geomBody[i]! m.geomFrame[i]! (part m.geomPosition 3 i) (part m.geomQuaternion 4 i)
    r := {r with geomPosition := put r.geomPosition 3 i pos,geomRotation := put r.geomRotation 9 i rot}
  for i in [:m.siteBody.size] do
    let (pos,rot) := localPose r m.siteBody[i]! m.siteFrame[i]! (part m.sitePosition 3 i) (part m.siteQuaternion 4 i)
    r := {r with sitePosition := put r.sitePosition 3 i pos,siteRotation := put r.siteRotation 9 i rot}
  return r
end FlyCNS.C3Kinematics
