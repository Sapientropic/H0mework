import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3KinematicsStep
set_option autoImplicit false
namespace FlyCNS.C3PlaneMesh
open FlyCNS.C3Actuation FlyCNS.C3Position FlyCNS.C3Kinematics

structure Material where
  mesh : Array Nat
  vertexStart : Array Nat
  vertexCount : Array Nat
  graphStart : Array Int
  graph : Array Int
  vertices : Array Float
  radius : Array Float
  pairFirst : Array Nat
  pairSecond : Array Nat
  margin : Array Float

structure Contact where
  pair : Nat
  distance : Float
  position : Array Float
  normal : Array Float
  vertex : Nat
  deriving Inhabited

def dot3 (a b : Array Float) : Float := fused a[2]! b[2]! (fused a[0]! b[0]! (a[1]!*b[1]!))
def transposeVector (m v : Array Float) : Array Float :=
  (List.range 3).toArray.map fun k => fused m[k+6]! v[2]! (fused m[k]! v[0]! (m[k+3]!*v[1]!))
def vertex (m : Material) (mesh index : Nat) : Array Float := part m.vertices 3 (m.vertexStart[mesh]!+index)

def support (m : Material) (mesh : Nat) (direction : Array Float) : Nat × Nat := Id.run do
  let graphAddress := m.graphStart[mesh]!
  if graphAddress < 0 || m.vertexCount[mesh]! < 10 then
    let mut best := 0
    let mut maximum := -(Float.ofBits 0x4202A05F20000000)
    for i in [:m.vertexCount[mesh]!] do
      let value := dot3 direction (vertex m mesh i)
      if value > maximum then maximum := value; best := i
    return (best,best)
  let base := graphAddress.toNat
  let n := m.graph[base]!.toNat
  let edgeBase := base+2+2*n
  let globalBase := base+2+n
  let mut best := 0
  let mut maximum := dot3 direction (vertex m mesh m.graph[globalBase]!.toNat)
  -- Each successful pass strictly increases a value selected from n vertices.
  for _ in [:n+1] do
    let mut edge := edgeBase+m.graph[base+2+best]!.toNat
    let mut changed := false
    while m.graph[edge]! >= 0 do
      let neighbor := m.graph[edge]!.toNat
      let value := dot3 direction (vertex m mesh m.graph[globalBase+neighbor]!.toNat)
      if value > maximum then maximum := value; best := neighbor; changed := true
      edge := edge+1
    if !changed then break
  return (best,m.graph[globalBase+best]!.toNat)

def makeContact (pair index : Nat) (point plane normal : Array Float) : Contact :=
  let distance := dot3 normal (subtract3 point plane)
  let scale := (Float.ofBits 0xBFE0000000000000)*distance
  ⟨pair,distance,(List.range 3).toArray.map (fun k => fused normal[k]! scale point[k]!),normal,index⟩

def generate (m : Material) (positions rotations : Array Float) : Array Contact := Id.run do
  let mut result := #[]
  for pair in [:m.pairFirst.size] do
    let first := m.pairFirst[pair]!
    let second := m.pairSecond[pair]!
    let plane := part positions 3 first
    let planeRotation := part rotations 9 first
    let normal := #[planeRotation[2]!,planeRotation[5]!,planeRotation[8]!]
    let direction := normal.map fun x => -x
    let rotation := part rotations 9 second
    let origin := part positions 3 second
    let localDirection := transposeVector rotation direction
    let mesh := m.mesh[second]!
    let (localIndex,index) := support m mesh localDirection
    let rawVertex := vertex m mesh index
    let sourceVertex := (List.range 3).toArray.map fun k => rawVertex[k]! + (localDirection[k]!*zero)/(Float.ofBits 0x4000000000000000)
    let point := add3 (matrixVector rotation sourceVertex) origin
    let contact := makeContact pair index point plane normal
    if contact.distance > m.margin[pair]! then continue
    result := result.push contact
    let threshold := dot3 normal (subtract3 origin plane)-m.margin[pair]!
    let mut count := 1
    let mut extra := #[]
    let graphAddress := m.graphStart[mesh]!
    if graphAddress < 0 then
      extra := (List.range m.vertexCount[mesh]!).toArray.filter fun i => i != localIndex
    else if m.vertexCount[mesh]! >= 10 then
      let base := graphAddress.toNat
      let n := m.graph[base]!.toNat
      let edgeBase := base+2+2*n
      let globalBase := base+2+n
      let mut edge := edgeBase+m.graph[base+2+localIndex]!.toNat
      while m.graph[edge]! >= 0 do
        extra := extra.push m.graph[globalBase+m.graph[edge]!.toNat]!.toNat
        edge := edge+1
    for i in extra do
      if count >= 3 then break
      let v := vertex m mesh i
      if dot3 localDirection v <= threshold then continue
      let p := add3 (matrixVector rotation v) origin
      if norm3 (subtract3 p contact.position) < (Float.ofBits 0x3FD3333333333333)*m.radius[second]! then continue
      result := result.push (makeContact pair i p plane normal)
      count := count+1
  return result
end FlyCNS.C3PlaneMesh
