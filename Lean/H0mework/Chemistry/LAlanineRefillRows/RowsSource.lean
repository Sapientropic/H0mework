import H0mework.Chemistry.LAlaninePropagation.BoundElectronicPropagation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.SourcePrimitive

open Propagation.Interface Propagation.Source

noncomputable def sourceGershDiagonal (i : Basis) : ℤ :=
  activeNumerator electronicSource i i -
    ∑ j : Basis, if i = j then 0 else |activeNumerator electronicSource i j|

noncomputable def sourceDensityRowMass (i : Basis) : ℤ :=
  ∑ j : Basis, symmetricEntry electronicSource.d0Q i j ^ 2

private def refillInputEntry (rows : Array (Array Int)) (column i j : Nat) : Int :=
  let lo := min i j
  let hi := max i j
  (rows[lo * (197 - lo) / 2 + hi - lo]!)[column]!

elab "lalanineRefillGershRows%" : term => do
  let rows ← sourceMatrixRows
  let h (i j : Nat) := 1000 * refillInputEntry rows 5 i j + refillInputEntry rows 8 i j
  let receipts := (List.range 98).map fun i =>
    let diagonal := h i i - ((List.range 98).map fun j => if i = j then 0 else |h i j|).sum
    let mass := ((List.range 98).map fun j => (refillInputEntry rows 9 i j) ^ 2).sum
    (diagonal, mass)
  return Lean.toExpr receipts.toArray

noncomputable def sourceCachedGershData : Array (Int × Int) := lalanineRefillGershRows%

noncomputable def sourceCachedGershDiagonal (i : Basis) : ℤ := (sourceCachedGershData[i.val]!).1
noncomputable def sourceCachedDensityRowMass (i : Basis) : ℤ := (sourceCachedGershData[i.val]!).2

end LAlanine40K2025.Thermal.Recovery.SourcePrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
