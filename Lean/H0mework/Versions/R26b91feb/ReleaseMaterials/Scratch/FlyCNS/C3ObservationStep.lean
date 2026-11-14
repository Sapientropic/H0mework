import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3GaitStep
set_option autoImplicit false
namespace FlyCNS.C3Observation
open FlyCNS.C3Actuation
structure Material where
  thorax : Nat
  tarsi : Array Nat
  detector : Array Int64
  ground : Nat
structure Frame where
  positions : Array Float
  rotations : Array Float
  geomFirst : Array Nat
  geomSecond : Array Nat
  exclude : Array Nat
  address : Array Int64
  friction : Array Float
  frames : Array Float
  force : Array Float
structure Result where
  observation : FlyCNS.C3Gait.Observation
  contactWrench : Array Float

/-- Same own contact force and body poses generate the original hybrid
observation; MuJoCo contactForce is not supplied or called. -/
def generate (m : Material) (f : Frame) : Result := Id.run do
  let mut forces := Array.replicate 54 zero
  let mut wrenches := #[]
  for c in [:f.geomFirst.size] do
    let mut wrench := Array.replicate 6 zero
    if f.address[c]! >= 0 then
      let a := f.address[c]!.toInt.toNat
      for i in [:4] do wrench := wrench.set! 0 (wrench[0]!+f.force[a+i]!)
      for i in [:2] do wrench := wrench.set! (i+1) ((f.force[a+2*i]!-f.force[a+2*i+1]!)*f.friction[5*c+i]!)
    wrenches := wrenches ++ wrench
    let first := f.geomFirst[c]!
    let second := f.geomSecond[c]!
    let firstPort := m.detector[first]!
    let secondPort := m.detector[second]!
    if f.exclude[c]! != 0 || !((firstPort >= 0 && second == m.ground) || (secondPort >= 0 && first == m.ground)) then continue
    let world := (List.range 3).toArray.map fun axis =>
      ((f.frames[9*c+axis]!*wrench[0]!)+(f.frames[9*c+3+axis]!*wrench[1]!))+
        f.frames[9*c+6+axis]!*wrench[2]!
    for axis in [:3] do
      if firstPort >= 0 then
        let i := firstPort.toInt.toNat*3+axis
        forces := forces.set! i (forces[i]!-world[axis]!)
      if secondPort >= 0 then
        let i := secondPort.toInt.toNat*3+axis
        forces := forces.set! i (forces[i]!+world[axis]!)
  let heading := #[f.rotations[9*m.thorax]!,f.rotations[9*m.thorax+3]!,f.rotations[9*m.thorax+6]!]
  return ⟨⟨f.positions[3*m.thorax+2]!,m.tarsi.map (fun i => f.positions[3*i+2]!),forces,heading⟩,wrenches⟩
end FlyCNS.C3Observation
