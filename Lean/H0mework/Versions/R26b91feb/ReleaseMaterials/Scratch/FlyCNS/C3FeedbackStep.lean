import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3OdorStep
set_option autoImplicit false
namespace FlyCNS.C3Feedback
open FlyCNS.C3Actuation

structure Material where
  odor : FlyCNS.C3Odor.Material
  populations : Array (Array Nat)
  innerSugar : Array Nat
  innerWater : Array Nat
  targets : Array Nat
  ligand : Array Nat
  signs : Array Int64
  peptideGain : Float
  pulseProbability : Float

structure Frame where
  points : Array Float
  gains : Array Float
  taste : Array Float
  peptide : Array Float
  receipts : Array Float

structure Result where
  stimulus : Array Nat
  probabilities : Array Float
  auxiliary : Array Nat
  currents : Array Int64
  odors : Array Float

/-- Source body/world coordinates generate the next original afferents.
Inner-mouth input comes only from positive actual receipts; signs/targets are
original receptor material, never a reward scalar or a desired action. -/
def generate (m : Material) (f : Frame) : Result := Id.run do
  let sampled := (List.range 3).toArray.map fun port =>
    FlyCNS.C3Odor.odor m.odor f.gains (f.points.extract (3*port) (3*port+3))
  let mut cells := #[]
  let mut probabilities := #[]
  let one := Float.ofBits 0x3ff0000000000000
  for cue in [:2] do
    for port in [:3] do
      let strength := sampled[port]![cue]!
      if strength > zero then
        for cell in m.populations[3*cue+port]! do
          cells := cells.push cell
          probabilities := probabilities.push (clip (strength*m.pulseProbability) zero one)
  for chemical in [:2] do
    if f.taste[chemical]! > zero then
      for cell in m.populations[6+chemical]! do
        cells := cells.push cell
        probabilities := probabilities.push (clip (f.taste[chemical]!*m.pulseProbability) zero one)
  if f.receipts[0]! > zero then
    cells := cells ++ m.innerSugar
    probabilities := probabilities ++ Array.replicate m.innerSugar.size (clip m.pulseProbability zero one)
  if f.receipts[1]! > zero then
    cells := cells ++ m.innerWater
    probabilities := probabilities ++ Array.replicate m.innerWater.size (clip m.pulseProbability zero one)
  let unique := (m.targets.toList.mergeSort (· ≤ ·)).eraseDups.toArray
  let mut drive := Array.replicate unique.size (0 : Int64)
  for i in [:m.targets.size] do
    let signed := (f.peptide[m.ligand[i]!]!*(FlyCNS.C3Integer.floatOfI m.signs[i]!))*m.peptideGain
    let current := FlyCNS.C3Integer.nearestEvenBits signed.toBits
    for j in [:unique.size] do
      if unique[j]! == m.targets[i]! then drive := drive.set! j (drive[j]!+current)
  let mut active := #[]
  let mut currents := #[]
  for j in [:unique.size] do
    if drive[j]! != 0 then
      active := active.push unique[j]!
      currents := currents.push drive[j]!
  return ⟨cells,probabilities,active,currents,sampled.foldl (· ++ ·) #[]⟩
end FlyCNS.C3Feedback
