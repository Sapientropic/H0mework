import H0mework.Chemistry.LAlanineTrueTubeHull.CacheReifier
import H0mework.Chemistry.LAlanineSourceMatrix.Aggregation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeHullCache

open Lean Elab Term Command

private def fieldRoot : Name :=
  ("SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.TrueTubeHullCache").toName

private def fin (value width : Nat) : TermElabM Expr := do
  let proof ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit width))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit width) (mkNatLit value) proof

private def equality (suffix : String) (left right : Expr) : TermElabM Unit := do
  let type ← Meta.mkEq left right
  let value ← Meta.mkEqRefl right
  let name := (← getCurrNamespace) ++ Name.mkSimple suffix
  addDecl (.thmDecl { name, levelParams := [], type, value })

private def proposition (suffix : String) (type : Expr) : TermElabM Unit := do
  let type ← Meta.whnf type
  let decider ← Meta.synthInstance (mkApp (Lean.mkConst ``Decidable) type)
  let truth ← Meta.mkEqRefl (Lean.mkConst ``Bool.true)
  let value := mkApp3 (Lean.mkConst ``of_decide_eq_true) type decider truth
  let name := (← getCurrNamespace) ++ Name.mkSimple suffix
  addDecl (.thmDecl { name, levelParams := [], type, value })

elab "checkTrueTubeHullGroup " field:num group:num : command => liftTermElabM do
  let f := field.getNat
  let i := group.getNat
  unless f == 0 && i < 94 do throwError "registered field/group"
  let root := fieldRoot
  let g ← fin i 94
  for a in [:3] do
    let axis ← fin a 3
    equality s!"relative_{i}_{a}"
      (mkApp2 (Lean.mkConst (root ++ `cachedRelative)) g axis)
      (mkApp2 (Lean.mkConst (root ++ `sourceRelative)) g axis)
  for (name, original) in [("radial", `sourceRadial), ("exp", `sourceExpFromRadial)] do
    let cached := if name == "radial" then `cachedRadial else `cachedExp
    equality s!"{name}_{i}" (mkApp (Lean.mkConst (root ++ cached)) g)
      (mkApp (Lean.mkConst (root ++ original)) g)
  proposition s!"reduction_{i}" (mkApp (Lean.mkConst (root ++ `reductionValid)) g)
  for a in [:3] do
    for p in [:3] do
      for n in [:3] do
        let axis ← fin a 3
        let power ← fin p 3
        let order ← fin n 3
        equality s!"poly_{i}_{a}_{p}_{n}"
          (mkApp4 (Lean.mkConst (root ++ `cachedPoly)) g axis power order)
          (mkApp4 (Lean.mkConst (root ++ `sourcePolyFromRelative)) g axis power order)

elab "checkTrueTubeHullAO " field:num basis:num : command => liftTermElabM do
  let f := field.getNat
  let i := basis.getNat
  unless f == 0 && i < 98 do throwError "registered field/AO"
  let root := fieldRoot
  let b ← fin i 98
  for j in [:10] do
    let jet ← fin j 10
    equality s!"ao_{i}_{j}" (mkApp2 (Lean.mkConst (root ++ `calculatedAO)) jet b)
      (mkApp2 (Lean.mkConst (root ++ `sourceAO)) jet b)

end LAlanine40K2025.BasinRefinement.TrueTubeHullCache
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
