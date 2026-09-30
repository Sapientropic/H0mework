import H0mework.Chemistry.LAlanineBandCache.Check

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCache

open Lean Elab Tactic

/-- Finite elimination only: each branch is an already kernel-checked row. -/
elab "closeWholeBandRows " count:num stem:str : tactic => do
  let goals ← getGoals
  unless goals.length == count.getNat do throwError "whole-band finite row census"
  let root ← getCurrNamespace
  for (goal,i) in goals.zipIdx do
    goal.assign (Lean.mkConst (root ++ Name.mkSimple (stem.getString ++ toString i)))
  setGoals []

end LAlanine40K2025.BasinRefinement.WholeBandCache
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
