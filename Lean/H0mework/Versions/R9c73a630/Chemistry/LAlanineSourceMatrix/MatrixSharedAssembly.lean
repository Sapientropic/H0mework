import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceMatrix.MatrixSharedCertificate

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices

open Lean Elab Tactic Term Command SourceIntegerGrid SourceFields SourceFiniteData

elab "closeRegisteredCells " stem:ident " fixed " pivot:num " width " rowSize:num : tactic => withMainContext do
  let goals ← getGoals
  unless goals.length == rowSize.getNat do throwError "complete source row census"
  for (goal,j) in goals.zipIdx do
    goal.assign (Lean.mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"{stem.getId.toString}_{pivot.getNat}_{j}"))
  setGoals []

private def sourceCommand (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error message => throwError "{message}"
  | .ok command => elabCommand command

elab "assembleRegisteredRow " index:num : command => do
  let i := index.getNat
  unless i < 10 do throwError "source low-jet row"
  sourceCommand s!"theorem first_row{i} (right : Basis) : firstAt {i} right =
    pointDot (aoMidRow {i}) (aoRadRow {i}) (PointColumns.column right) := by
    fin_cases right
    closeRegisteredCells firstFast fixed {i} width 98"
  sourceCommand s!"theorem bilinear_row{i} (right : LowJet) : bilinearAt {i} right =
    dotList (firstRow {i}) (aoRow right) := by
    fin_cases right
    closeRegisteredCells bilinear fixed {i} width 10"
  sourceCommand s!"theorem ao_grid_row{i} (right : Basis) : grid (aoAt {i} right) =
    SourceFields.AllFields.calculatedAO fieldIndex {i} right := by
    fin_cases right
    closeRegisteredCells ao fixed {i} width 98"

elab "closeRegisteredRows " stem:ident " at " arg:term : tactic => withMainContext do
  let value ← Term.elabTerm arg none
  let goals ← getGoals
  unless goals.length == 10 do throwError "complete low-jet source census"
  for (goal,i) in goals.zipIdx do
    goal.assign (mkApp (Lean.mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"{stem.getId.toString}{i}")) value)
  setGoals []

elab "closeRegisteredConstantRows " stem:ident : tactic => do
  let goals ← getGoals
  unless goals.length == 10 do throwError "complete prepared row census"
  for (goal,i) in goals.zipIdx do
    goal.assign (Lean.mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"{stem.getId.toString}{i}"))
  setGoals []

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices
