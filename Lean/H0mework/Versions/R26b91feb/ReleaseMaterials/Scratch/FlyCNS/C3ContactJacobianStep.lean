import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3InertiaStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3SparseStep
set_option autoImplicit false
namespace FlyCNS.C3ContactJacobian
open FlyCNS.C3Actuation FlyCNS.C3Kinematics

structure Material where
  geomBody : Array Nat
  bodyWeld : Array Nat
  bodyRoot : Array Nat
  bodyDofStart : Array Int
  bodyDofCount : Array Nat
  dofParent : Array Int

structure Frame where
  center : Array Float
  motion : Array Float
  geomFirst : Array Nat
  geomSecond : Array Nat
  positions : Array Float
  frames : Array Float
  friction : Array Float
  distance : Array Float
  margin : Array Float
  exclude : Array Nat

structure Result where
  jacobian : FlyCNS.C3Sparse.Matrix
  position : Array Float
  margin : Array Float
  contact : Array Nat
  contactAddress : Array Int

def chain (m : Material) (body : Nat) : Array Nat := Id.run do
  let weld := m.bodyWeld[body]!
  if weld == 0 then return #[]
  let mut j := m.bodyDofStart[weld]!+(m.bodyDofCount[weld]! : Int)-1
  let mut result := #[]
  while j >= 0 do
    result := result.push j.toNat
    j := m.dofParent[j.toNat]!
  return result.reverse

def generate (m : Material) (f : Frame) : Result := Id.run do
  let mut values := #[]
  let mut columns := #[]
  let mut starts := #[]
  let mut counts := #[]
  let mut positions := #[]
  let mut margins := #[]
  let mut contacts := #[]
  let mut addresses : Array Int := Array.replicate f.geomFirst.size (-1)
  for c in [:f.geomFirst.size] do
    if f.exclude[c]! != 0 then continue
    let body := m.geomBody[f.geomSecond[c]!]!
    let ancestors := chain m body
    if ancestors.isEmpty then continue
    let count := ancestors.size
    let offset := subtract3 (part f.positions 3 c) (part f.center 3 m.bodyRoot[body]!)
    let mut jacobian := Array.replicate (3*count) zero
    for k in [:count] do
      let v := part f.motion 6 ancestors[k]!
      let cross := FlyCNS.C3Inertia.cross (v.extract 0 3) offset
      for axis in [:3] do jacobian := jacobian.set! (axis*count+k) (v[3+axis]!+cross[axis]!-zero)
    let rotation := part f.frames 9 c
    let mut rotated := Array.replicate (3*count) zero
    for axis in [:3] do
      for k in [:3] do
        if rotation[3*axis+k]! != zero then
          for j in [:count] do rotated := rotated.set! (axis*count+j) (fused rotation[3*axis+k]! jacobian[k*count+j]! rotated[axis*count+j]!)
    addresses := addresses.set! c starts.size
    for tangent in [1:3] do
      for side in [:2] do
        starts := starts.push values.size
        counts := counts.push count
        for j in [:count] do
          let coefficient := if side == 0 then f.friction[5*c+tangent-1]! else -f.friction[5*c+tangent-1]!
          values := values.push (fused coefficient rotated[tangent*count+j]! rotated[j]!)
          columns := columns.push ancestors[j]!
        positions := positions.push f.distance[c]!
        margins := margins.push f.margin[c]!
        contacts := contacts.push c
  return ⟨⟨starts.size,74,values,starts,counts,columns⟩,positions,margins,contacts,addresses⟩
end FlyCNS.C3ContactJacobian
