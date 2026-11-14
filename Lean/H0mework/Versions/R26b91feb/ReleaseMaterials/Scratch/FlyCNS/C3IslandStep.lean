import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3TransmissionStep
set_option autoImplicit false
namespace FlyCNS.C3Island
open FlyCNS.C3Actuation
structure Material where
  transmission : FlyCNS.C3Transmission.Material
  bodyTree : Array Int64
  dofTree : Array Nat
structure Result where
  transmission : FlyCNS.C3Transmission.Result
  islandCount : Nat
  dofCount : Nat
  dofMap : Array Nat
  constraintMap : Array Nat

/-- Original rigid contacts link the static world to the one actual articulated
source tree. No completed island labels or permutation are input. -/
def generate (m : Material) (f : FlyCNS.C3Transmission.Frame) : Result := Id.run do
  let r := FlyCNS.C3Transmission.generate m.transmission f
  if r.current.contact.jacobian.rows == 0 then return ⟨r,0,0,#[],#[]⟩
  let mut attached := false
  for c in [:f.contactCurrent.contact.geomFirst.size] do
    if r.current.contact.contactAddress[c]! >= 0 then
      let first := m.transmission.contacts.jacobian.geomBody[f.contactCurrent.contact.geomFirst[c]!]!
      let second := m.transmission.contacts.jacobian.geomBody[f.contactCurrent.contact.geomSecond[c]!]!
      if m.bodyTree[first]! == 0 || m.bodyTree[second]! == 0 then attached := true
  if !attached then return ⟨r,0,0,#[],#[]⟩
  return ⟨r,1,m.dofTree.size,(List.range m.dofTree.size).toArray,
    (List.range r.current.contact.jacobian.rows).toArray⟩
end FlyCNS.C3Island
