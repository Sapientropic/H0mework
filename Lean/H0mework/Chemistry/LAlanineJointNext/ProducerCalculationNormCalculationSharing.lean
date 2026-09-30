import H0mework.Chemistry.LAlanineJointNext.ProducerCoefficients

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.NormCalculation

open Lean Elab Term Command

partial def listEntries (value : Expr) (entries : Array Expr := #[]) : Option (Array Expr) :=
  if value.isAppOfArity ``List.nil 1 then some entries
  else if value.isAppOfArity ``List.cons 3 then
    listEntries (value.getArg! 2) (entries.push (value.getArg! 1))
  else none

def matrixValues (name : Name) : MetaM (Array (Array Int)) := do
  let value := (← getConstInfo name).value!
  let rows ← Meta.whnf value.appArg!
  let some rowExpressions := listEntries (rows.getArg! 1) | throwError "Nonliteral matrix rows"
  rowExpressions.mapM fun row => do
    let row ← Meta.whnf row
    let some entries := listEntries (row.getArg! 1) | throwError "Nonliteral matrix row"
    entries.mapM fun entry => do
      let some number ← Meta.getIntValue? entry | throwError "Nonliteral integer coefficient"
      pure number

private def sharedDeclaration (name : Name) (value : Expr) : TermElabM Unit := do
  let type ← Meta.inferType value
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

/-- Row constants share the original declaration's expressions; `Eq.refl` checks the complete reader. -/
elab "shareJointCalculationRows" : command => liftTermElabM do
  for (source, suffix) in [(``Source.crossNumerator, `crossNumerator),
      (``Source.hamiltonianNumerator, `hamiltonianNumerator),
      (``Source.targetRealNumerator, `targetRealNumerator),
      (``Source.targetImagNumerator, `targetImagNumerator),
      (``HeldForce.Source.gammaNumerator, `gammaNumerator)] do
    let original := (← getConstInfo source).value!
    let array ← Meta.whnf original.appArg!
    unless array.isAppOfArity ``Array.mk 2 do
      throwError "Source row head {array.getAppFn} / {array.getAppNumArgs}: {source}"
    let some rows := listEntries (array.getArg! 1) | throwError "Source row list is not literal: {source}"
    unless rows.size == 98 do throwError "Source row census changed: {source}"
    let name := (← getCurrNamespace) ++ suffix
    let mut references := #[]
    for i in [:rows.size] do
      let rowName := name ++ Name.mkSimple s!"row{i}"
      sharedDeclaration rowName (← Meta.whnf rows[i]!)
      references := references.push (Lean.mkConst rowName)
    let sharedRows ← Meta.mkArrayLit (← Meta.inferType rows[0]!) references.toList
    sharedDeclaration name (mkApp original.appFn! (← Meta.whnf sharedRows))
    let equality ← Meta.mkEq (Lean.mkConst source) (Lean.mkConst name)
    let proof ← Meta.mkEqRefl (Lean.mkConst source)
    let theoremName := (← getCurrNamespace) ++ Name.mkSimple s!"{suffix}_eq"
    addDecl (.thmDecl {
      name := theoremName
      levelParams := [], type := equality, value := proof })

set_option maxRecDepth 2048 in
shareJointCalculationRows

end LAlanine40K2025.JointNext.NormCalculation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
