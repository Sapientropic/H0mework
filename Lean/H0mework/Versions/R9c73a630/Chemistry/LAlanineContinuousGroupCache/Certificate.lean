import H0mework.Versions.AB.Chemistry.LAlanineContinuousGroupCache.Data

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGroupCache

open Lean Elab Term Command Tactic SourceRectangle SourceSignedEvaluator

private def fin (value width : Nat) : TermElabM Expr := do
  let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit width))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit width) (mkNatLit value) inside

private def certify (suffix : String) (left right : Expr) : TermElabM Unit := do
  let type ← Meta.mkEq left right
  let value ← Meta.mkEqRefl right
  addDecl (.thmDecl { name := (← getCurrNamespace) ++ Name.mkSimple suffix, levelParams := [], type, value })

elab "checkSourceGroup " index:num : command => liftTermElabM do
  let i := index.getNat
  unless i < 94 do throwError "actual source group index"
  let g ← fin i 94
  for a in [:3] do
    let axis ← fin a 3
    certify s!"relative_{i}_{a}"
      (mkApp2 (Lean.mkConst ``cachedRelative) g axis) (mkApp2 (Lean.mkConst ``sourceRelative) g axis)
  certify s!"radial_{i}" (mkApp (Lean.mkConst ``cachedRadial) g) (mkApp (Lean.mkConst ``sourceRadial) g)
  certify s!"exp_{i}" (mkApp (Lean.mkConst ``cachedExp) g) (mkApp (Lean.mkConst ``sourceExpFromRadial) g)
  for a in [:3] do
    for p in [:3] do
      for n in [:4] do
        let axis ← fin a 3
        let power ← fin p 3
        let order ← fin n 4
        certify s!"poly_{i}_{a}_{p}_{n}"
          (mkApp4 (Lean.mkConst ``cachedPoly) g axis power order)
          (mkApp4 (Lean.mkConst ``sourcePolyFromRelative) g axis power order)

elab "closeSourceGroupRelative " index:num : tactic => do
  let goals ← getGoals
  unless goals.length == 3 do throwError "three registered axes required"
  for (goal, axis) in goals.zipIdx do
    goal.assign (Lean.mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"relative_{index.getNat}_{axis}"))
  setGoals []

elab "closeSourceGroupPoly " index:num : tactic => do
  let goals ← getGoals
  unless goals.length == 36 do throwError "three axes, three powers and four orders required"
  for (goal, flat) in goals.zipIdx do
    let axis := flat / 12
    let power := (flat / 4) % 3
    let order := flat % 4
    goal.assign (Lean.mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"poly_{index.getNat}_{axis}_{power}_{order}"))
  setGoals []

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGroupCache
