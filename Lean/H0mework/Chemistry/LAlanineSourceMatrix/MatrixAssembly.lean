import H0mework.Chemistry.LAlanineSourceMatrix.MatrixCertificate

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceField1Matrix

open Lean Elab Tactic Term Command SourceIntegerGrid SourceFields SourceFiniteData

elab "closeField1Cells " stem:ident " fixed " pivot:num " width " rowSize:num : tactic => withMainContext do
  let goals ← getGoals
  unless goals.length == rowSize.getNat do throwError "complete field1 source row"
  for (goal, j) in goals.zipIdx do
    goal.assign (Lean.mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"{stem.getId.toString}_{pivot.getNat}_{j}"))
  setGoals []

private def sourceCommand (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error message => throwError "{message}"
  | .ok command => elabCommand command

elab "assembleField1Row " index:num : command => do
  let i := index.getNat
  unless i < 10 do throwError "field1 low-jet row"
  sourceCommand s!"theorem first_row{i} (right : Basis) : firstAt {i} right =
    dotList (aoRow {i}) (SourceIntegerMatrix.densityColumn right) := by
    fin_cases right
    closeField1Cells first fixed {i} width 98"
  sourceCommand s!"theorem bilinear_row{i} (right : LowJet) : bilinearAt {i} right =
    dotList (firstRow {i}) (aoRow right) := by
    fin_cases right
    closeField1Cells bilinear fixed {i} width 10"
  sourceCommand s!"theorem ao_grid_row{i} (right : Basis) : grid (aoAt {i} right) =
    SourceFields.Field1.calculatedAO {i} right := by
    fin_cases right
    closeField1Cells ao fixed {i} width 98"

elab "closeField1Rows " stem:ident " at " arg:term : tactic => withMainContext do
  let value ← Term.elabTerm arg none
  let goals ← getGoals
  unless goals.length == 10 do throwError "complete low-jet census"
  for (goal, i) in goals.zipIdx do
    goal.assign (mkApp (Lean.mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"{stem.getId.toString}{i}")) value)
  setGoals []

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceField1Matrix
