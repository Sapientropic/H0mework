import H0mework.Versions.AB.Chemistry.LAlanineBandCache.Reifier

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCache

open Lean Elab Term Command

private def fin (value bound : Nat) : TermElabM Expr := do
  let proof ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit bound))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit bound) (mkNatLit value) proof

private def exactComputation (type : Expr) : TermElabM Expr := do
  let type ← Meta.whnf type
  if type.isAppOfArity ``Eq 3 then
    return ← Meta.mkEqRefl type.getAppArgs[2]!
  let decider ← Meta.synthInstance (mkApp (Lean.mkConst ``Decidable) type)
  return mkApp3 (Lean.mkConst ``of_decide_eq_true) type decider
    (← Meta.mkEqRefl (Lean.mkConst ``Bool.true))

/-- One kernel-checked row retains all 27 polynomial coordinates. -/
elab "checkWholeBandGroups " start:num stop:num : command => liftTermElabM do
  let first := start.getNat
  let last := stop.getNat
  unless first ≤ last && last ≤ 94 do throwError "registered group range"
  let root ← getCurrNamespace
  let box := Lean.mkConst (root ++ `localBox)
  let reductions := Lean.mkConst (root ++ `localReductions)
  let material := Lean.mkConst (root ++ `material)
  for i in [first:last] do
    let g ← fin i 94
    let type := mkApp4 (Lean.mkConst ``GroupComputed) box reductions material g
    let goal ← Meta.mkFreshExprMVar type
    let fields ← goal.mvarId!.apply (Lean.mkConst ``GroupComputed.mk)
    for field in fields do
      field.assign (← exactComputation (← field.getType))
    let value ← instantiateMVars goal
    addDecl (.thmDecl { name := root ++ Name.mkSimple s!"group{i}", levelParams := [], type, value })

elab "checkWholeBandOrbitals " start:num stop:num : command => liftTermElabM do
  let first := start.getNat
  let last := stop.getNat
  unless first ≤ last && last ≤ 98 do throwError "registered AO range"
  let root ← getCurrNamespace
  for i in [first:last] do
    let type := mkApp3 (Lean.mkConst ``OrbitalComputed) (Lean.mkConst (root ++ `localBox))
      (Lean.mkConst (root ++ `material)) (← fin i 98)
    let value ← exactComputation type
    addDecl (.thmDecl { name := root ++ Name.mkSimple s!"orbital{i}", levelParams := [], type, value })

end LAlanine40K2025.BasinRefinement.WholeBandCache
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
