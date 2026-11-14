import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ExpROM
set_option autoImplicit false
namespace FlyCNS.C3Odor
open FlyCNS.C3Actuation
structure Material where
  positions : Array (Array Float)
  sigma : Array Float
  strengths : Array (Array Float)
def odor (m : Material) (gain point : Array Float) : Array Float := Id.run do
  let mut result := #[zero,zero]
  for source in [:m.sigma.size] do
    let delta := point.mapIdx fun i value => value-m.positions[source]![i]!
    let square := ((delta[0]!*delta[0]!)+(delta[1]!*delta[1]!))+(delta[2]!*delta[2]!)
    let gaussian := FlyCNS.C3Exp.exponential (-square / ((Float.ofBits 0x4000000000000000)*(m.sigma[source]!*m.sigma[source]!)))
    result := result.mapIdx fun i value => value+m.strengths[source]![i]!*gaussian
  return result.mapIdx fun i value => clip (value*gain[i]!) zero (Float.ofBits 0x3FF0000000000000)
end FlyCNS.C3Odor
