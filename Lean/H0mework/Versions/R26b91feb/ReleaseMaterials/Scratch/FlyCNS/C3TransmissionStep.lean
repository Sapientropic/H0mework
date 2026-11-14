import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ContactCurrentStep
set_option autoImplicit false
namespace FlyCNS.C3Transmission
open FlyCNS.C3Actuation FlyCNS.C3Kinematics FlyCNS.C3Sparse

structure Material where
  contacts : FlyCNS.C3ContactCurrent.Material
  actuatorType : Array Nat
  target : Array Nat
  gear : Array Float
  jointAddress : Array Nat
  jointDof : Array Nat

structure Frame where
  contactCurrent : FlyCNS.C3ContactCurrent.Frame
  qpos : Array Float

structure Result where
  current : FlyCNS.C3ContactCurrent.Result
  lengths : Array Float
  moments : Matrix

/-- Original active/excluded contact normal in the body's sparse ancestor chain. -/
def contactNormal (m : FlyCNS.C3ContactJacobian.Material)
    (f : FlyCNS.C3ContactJacobian.Frame) (c : Nat) : Array Float := Id.run do
  let body := m.geomBody[f.geomSecond[c]!]!
  let ancestors := FlyCNS.C3ContactJacobian.chain m body
  let count := ancestors.size
  let offset := subtract3 (part f.positions 3 c) (part f.center 3 m.bodyRoot[body]!)
  let mut jac := Array.replicate (3*count) zero
  for k in [:count] do
    let v := part f.motion 6 ancestors[k]!
    let cross := FlyCNS.C3Inertia.cross (v.extract 0 3) offset
    for axis in [:3] do jac := jac.set! (axis*count+k) (v[3+axis]!+cross[axis]!-zero)
  let mut normal := Array.replicate count zero
  for axis in [:3] do
    let scale := f.frames[9*c+axis]!
    if scale != zero then
      for k in [:count] do normal := normal.set! k (fused scale jac[axis*count+k]! normal[k]!)
  return normal

/-- All 44 hinge and six native body-adhesion transmissions are generated
from qpos and the same own contacts/J, not from an actuator moment oracle. -/
def generate (m : Material) (f : Frame) : Result := Id.run do
  let current := FlyCNS.C3ContactCurrent.generate m.contacts f.contactCurrent
  let contact := f.contactCurrent.contact
  let j := current.contact.jacobian
  let mut values := #[]
  let mut starts := #[]
  let mut counts := #[]
  let mut columns := #[]
  let mut lengths := #[]
  for actuator in [:m.actuatorType.size] do
    starts := starts.push values.size
    let target := m.target[actuator]!
    if m.actuatorType[actuator]! == 0 then
      lengths := lengths.push (f.qpos[m.jointAddress[target]!]!*m.gear[6*actuator]!)
      values := values.push m.gear[6*actuator]!
      columns := columns.push m.jointDof[target]!
      counts := counts.push 1
    else
      lengths := lengths.push zero
      let mut force := Array.replicate j.rows zero
      let mut excluded := Array.replicate 74 zero
      let mut counter := 0
      for c in [:contact.geomFirst.size] do
        let first := m.contacts.jacobian.geomBody[contact.geomFirst[c]!]!
        let second := m.contacts.jacobian.geomBody[contact.geomSecond[c]!]!
        if first != target && second != target then continue
        if contact.exclude[c]! == 0 then
          counter := counter+1
          let address := current.contact.contactAddress[c]!.toNat
          for k in [:4] do force := force.set! (address+k) (Float.ofBits 0x3fd0000000000000)
        else if contact.exclude[c]! == 1 then
          counter := counter+1
          let normal := contactNormal m.contacts.jacobian contact c
          let chain := FlyCNS.C3ContactJacobian.chain m.contacts.jacobian second
          for k in [:chain.size] do excluded := excluded.set! chain[k]! (excluded[chain[k]!]!+normal[k]!)
      let mut moment := Array.replicate 74 zero
      if counter != 0 then
        moment := transposeScatterMultiply j force
        let scale := -FlyCNS.C3ContactCurrent.one/(UInt64.ofNat counter).toFloat
        moment := moment.mapIdx fun k v => (v+excluded[k]!)*scale
      let first := values.size
      for k in [:74] do
        if moment[k]! != zero then
          columns := columns.push k
          values := values.push moment[k]!
      counts := counts.push (values.size-first)
  return ⟨current,lengths,⟨m.actuatorType.size,74,values,starts,counts,columns⟩⟩
end FlyCNS.C3Transmission
