import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3KinematicsStep

/-! Original mj_comPos/mj_crb/mj_makeM, consuming generated Cartesian poses.
The full current constructor below generates those poses from qpos itself. -/
set_option autoImplicit false
namespace FlyCNS.C3Inertia
open FlyCNS.C3Actuation FlyCNS.C3Position FlyCNS.C3Kinematics

structure Material where
  parent : Array Nat
  root : Array Nat
  jointStart : Array Nat
  jointCount : Array Nat
  jointType : Array Nat
  dofAddress : Array Nat
  mass : Array Float
  subtreeMass : Array Float
  inertia : Array Float
  dofBody : Array Nat
  dofParent : Array Int
  armature : Array Float
  rowStart : Array Nat
  rowCount : Array Nat
  legacyMap : Array Nat

structure Result where
  center : Array Float
  inertia : Array Float
  motion : Array Float
  composite : Array Float
  matrix : Array Float
  legacyMatrix : Array Float

def cross (a b : Array Float) : Array Float :=
  #[fused a[1]! b[2]! ((-a[2]!)*b[1]!),fused a[2]! b[0]! ((-a[0]!)*b[2]!),
    fused a[0]! b[1]! ((-a[1]!)*b[0]!)]

def inertCom (i r v : Array Float) (mass : Float) : Array Float :=
  let t := #[r[0]!*i[0]!,r[3]!*i[0]!,r[6]!*i[0]!,r[1]!*i[1]!,r[4]!*i[1]!,r[7]!*i[1]!,
    r[2]!*i[2]!,r[5]!*i[2]!,r[8]!*i[2]!]
  let d := fun a b c x y z : Float => fused c z (fused a x (b*y))
  let yy := v[1]!*v[1]!; let zz := v[2]!*v[2]!
  #[fused mass (fused v[1]! v[1]! zz) (d r[0]! r[1]! r[2]! t[0]! t[3]! t[6]!),
    fused mass (fused v[0]! v[0]! zz) (d r[3]! r[4]! r[5]! t[1]! t[4]! t[7]!),
    fused mass (fused v[0]! v[0]! yy) (d r[6]! r[7]! r[8]! t[2]! t[5]! t[8]!),
    fused (mass*(-v[0]!)) v[1]! (d r[0]! r[1]! r[2]! t[1]! t[4]! t[7]!),
    fused (mass*(-v[0]!)) v[2]! (d r[0]! r[1]! r[2]! t[2]! t[5]! t[8]!),
    fused (mass*(-v[1]!)) v[2]! (d r[3]! r[4]! r[5]! t[2]! t[5]! t[8]!),
    mass*v[0]!,mass*v[1]!,mass*v[2]!,mass]

def multiply (i v : Array Float) : Array Float :=
  #[fused i[7]! v[5]! (fused (-i[8]!) v[4]! (fused i[4]! v[2]! (fused i[0]! v[0]! (i[3]!*v[1]!)))),
    fused (-i[6]!) v[5]! (fused i[8]! v[3]! (fused i[5]! v[2]! (fused i[3]! v[0]! (i[1]!*v[1]!)))),
    fused i[6]! v[4]! (fused (-i[7]!) v[3]! (fused i[2]! v[2]! (fused i[4]! v[0]! (i[5]!*v[1]!)))),
    fused i[9]! v[3]! (fused i[8]! v[1]! ((-i[7]!)*v[2]!)),
    fused i[9]! v[4]! (fused i[6]! v[2]! ((-i[8]!)*v[0]!)),
    fused i[9]! v[5]! (fused i[7]! v[0]! ((-i[6]!)*v[1]!))]

def dot6 (a b : Array Float) : Float :=
  ((fused a[0]! b[0]! (a[2]!*b[2]!))+(fused a[1]! b[1]! (a[3]!*b[3]!)))+
    (fused a[4]! b[4]! (a[5]!*b[5]!))

def fromPose (m : Material) (pose : FlyCNS.C3Kinematics.Result) : Result := Id.run do
  let n := m.parent.size
  let nv := m.dofBody.size
  let mut center := (List.range (3*n)).toArray.map fun k => pose.inertiaPosition[k]!*m.mass[k/3]!
  for back in [:n-1] do
    let i := n-back-1
    let parent := m.parent[i]!
    center := put center 3 parent (add3 (part center 3 parent) (part center 3 i))
  for i in [:n] do
    let value := if m.subtreeMass[i]! < minimum then part pose.inertiaPosition 3 i
      else (part center 3 i).map fun x => x*(one/m.subtreeMass[i]!)
    center := put center 3 i value
  let mut inertia := Array.replicate (10*n) zero
  for i in [1:n] do
    let offset := subtract3 (part pose.inertiaPosition 3 i) (part center 3 m.root[i]!)
    inertia := put inertia 10 i (inertCom (part m.inertia 3 i) (part pose.inertiaRotation 9 i) offset m.mass[i]!)
  let mut motion := Array.replicate (6*nv) zero
  for i in [1:n] do
    for j in [m.jointStart[i]!:m.jointStart[i]!+m.jointCount[i]!] do
      let address := m.dofAddress[j]!
      let offset := subtract3 (part center 3 m.root[i]!) (part pose.anchor 3 j)
      if m.jointType[j]! == 0 then
        for k in [:3] do motion := motion.set! (6*(address+k)+3+k) one
        let rotation := part pose.rotation 9 i
        for k in [:3] do
          let axis := #[rotation[k]!,rotation[k+3]!,rotation[k+6]!]
          motion := put motion 6 (address+3+k) (axis ++ cross axis offset)
      else
        let axis := part pose.axis 3 j
        motion := put motion 6 address (axis ++ cross axis offset)
  let mut composite := inertia
  for back in [:n] do
    let i := n-back-1
    let parent := m.parent[i]!
    if parent != 0 then
      for k in [:10] do composite := composite.set! (10*parent+k) (composite[10*parent+k]!+composite[10*i+k]!)
  let mut matrix := Array.replicate m.legacyMap.size zero
  for i in [:nv] do
    let mut address := m.rowStart[i]!+m.rowCount[i]!-1
    matrix := matrix.set! address (m.armature[i]!+zero)
    let buffer := multiply (part composite 10 m.dofBody[i]!) (part motion 6 i)
    let mut j : Int := i
    while j >= 0 do
      let v := j.toNat
      matrix := matrix.set! address (matrix[address]!+dot6 (part motion 6 v) buffer)
      address := address-1
      j := m.dofParent[v]!
  let mut legacy := Array.replicate matrix.size zero
  for i in [:matrix.size] do legacy := legacy.set! m.legacyMap[i]! matrix[i]!
  return ⟨center,inertia,motion,composite,matrix,legacy⟩

def fromPosition (kinematics : FlyCNS.C3Kinematics.Material) (m : Material) (qpos : Array Float) : Result :=
  fromPose m (FlyCNS.C3Kinematics.generate kinematics qpos)
end FlyCNS.C3Inertia
