import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Cut
import Mathlib.Data.Fintype.Fin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network

private abbrev Arc := Nat × Nat
private abbrev Residual := Array ℚ

private def read (width : Nat) (residual : Residual) (arc : Arc) : ℚ :=
  residual.getD (arc.1 * width + arc.2) 0

private def write (width : Nat) (residual : Residual) (arc : Arc) (capacity : ℚ) : Residual :=
  residual.setIfInBounds (arc.1 * width + arc.2) capacity

private inductive Search where
  | path (arcs : List Arc)
  | cut (reachable : List Nat)
  | exhausted

private def findPath (vertices : List Nat) (width sink : Nat) (residual : Residual) :
    Nat → List (Nat × List Arc) → List Nat → Search
  | _, [], reached => .cut reached
  | 0, _ :: _, _ => .exhausted
  | fuel + 1, (current, path) :: rest, reached =>
      if current = sink then .path path
      else
        let fresh := vertices.filter fun target =>
          !reached.contains target && decide (0 < read width residual (current, target))
        let queue := rest ++ fresh.map fun target => (target, (current, target) :: path)
        findPath vertices width sink residual fuel queue (reached ++ fresh)

private def bottleneck (width : Nat) (residual : Residual) (ceiling : ℚ) (path : List Arc) : ℚ :=
  path.foldl (fun current arc => min current (read width residual arc)) ceiling

private def augment (width : Nat) (residual : Residual) (quantity : ℚ) (path : List Arc) : Residual :=
  path.foldl (fun graph arc =>
    let reverse := (arc.2, arc.1)
    let forwardCapacity := read width graph arc - quantity
    let backwardCapacity := read width graph reverse + quantity
    write width (write width graph arc forwardCapacity) reverse backwardCapacity) residual

private def run (vertices : List Nat) (width sink : Nat) (ceiling : ℚ) :
    Nat → Residual → Option (Residual × List Nat)
  | fuel, residual =>
      match findPath vertices width sink residual width [(0, [])] [0] with
      | .cut reached => some (residual, reached)
      | .exhausted => none
      | .path path =>
          match fuel with
          | 0 => none
          | remaining + 1 =>
              let quantity := bottleneck width residual ceiling path
              if 0 < quantity then
                run vertices width sink ceiling remaining (augment width residual quantity path)
              else none

private def initialCapacity {left right : Nat}
    (network : Network (Fin left) (Fin right)) (ceiling : ℚ) (sourceNode targetNode : Nat) : ℚ :=
  if sourceNode = 0 then
    if valid : 0 < targetNode ∧ targetNode ≤ left then network.need ⟨targetNode - 1, by omega⟩ else 0
  else if validLeft : 0 < sourceNode ∧ sourceNode ≤ left then
    if validRight : left < targetNode ∧ targetNode ≤ left + right then
      if network.allows ⟨sourceNode - 1, by omega⟩ ⟨targetNode - left - 1, by omega⟩ then ceiling else 0
    else 0
  else if validRight : left < sourceNode ∧ sourceNode ≤ left + right then
    if targetNode = left + right + 1 then network.capacity ⟨sourceNode - left - 1, by omega⟩ else 0
  else 0

/-- Exact rational shortest augmenting paths. The producer's output always
passes the independent original allocation/cut checker before it can be used. -/
def fast {left right : Nat} (network : Network (Fin left) (Fin right)) : Option (network.Certificate) := do
  let width := left + right + 2
  let vertices := List.range width
  let ceiling := network.demandOf Finset.univ
  let initial := (vertices.flatMap fun sourceNode =>
    vertices.map fun targetNode => initialCapacity network ceiling sourceNode targetNode).toArray
  let arcCount := left + right + left * right
  let (residual, reachable) ← run vertices width (width - 1) ceiling (width * (2 * arcCount + 1)) initial
  let allocation := fun slot item => read width residual (left + item.val + 1, slot.val + 1)
  let group := Finset.univ.filter fun slot : Fin left => reachable.contains (slot.val + 1)
  network.check allocation group

end SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network
