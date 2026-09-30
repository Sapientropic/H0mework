import H0mework.Chemistry.LAlanineContinuousMatrix.IntegerDataCertificate
import H0mework.Chemistry.LAlanineContinuousMatrix.IntegerDataIncidenceCertificate

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerMatrix

open Lean Elab Tactic Term Command SourceIntegerGrid SourceRectangle SourceFiniteData

elab "closeIntegerCells " stem:ident " fixed " fixed:num " width " width:num " transposed " transposed:num : tactic => withMainContext do
  let goals ← getGoals
  unless goals.length == width.getNat do throwError "integer source row census"
  for (goal, varying) in goals.zipIdx do
    let first := if transposed.getNat == 0 then fixed.getNat else varying
    let second := if transposed.getNat == 0 then varying else fixed.getNat
    let name := (← getCurrNamespace) ++ Name.mkSimple s!"{stem.getId.toString}_{first}_{second}"
    goal.assign (Lean.mkConst name)
  setGoals []

private def sourceCommand (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error message => throwError "{message}"
  | .ok command => elabCommand command

elab "assembleIntegerRow " index:num : command => do
  let i := index.getNat
  unless i < 20 do throwError "integer source derivative row"
  sourceCommand s!"theorem first_row{i} (right : Basis) : firstAt {i} right =
    dotList (aoRow {i}) (densityColumn right) := by
    fin_cases right
    closeIntegerCells first fixed {i} width 98 transposed 0"
  sourceCommand s!"theorem bilinear_row{i} (right : Jet) : bilinearAt {i} right =
    dotList (firstRow {i}) (aoRow right) := by
    fin_cases right
    closeIntegerCells bilinear fixed {i} width 20 transposed 0"
  sourceCommand s!"theorem ao_grid_row{i} (right : Basis) : grid (aoAt {i} right) =
    SourceRectangleChecks.calculatedAO {i} right := by
    fin_cases right
    closeIntegerCells ao_grid fixed {i} width 98 transposed 0"
  sourceCommand s!"theorem first_grid_row{i} (right : Basis) : grid (firstAt {i} right) =
    SourceSignedMatrix.calculatedFirst {i} right := by
    fin_cases right
    closeIntegerCells first_grid fixed {i} width 98 transposed 0"
  sourceCommand s!"theorem bilinear_grid_row{i} (right : Jet) : grid (bilinearAt {i} right) =
    SourceSignedMatrix.calculatedBilinear {i} right := by
    fin_cases right
    closeIntegerCells bilinear_grid fixed {i} width 20 transposed 0"

elab "assembleIntegerColumn " index:num : command => do
  let j := index.getNat
  unless j < 98 do throwError "original density column"
  sourceCommand s!"theorem density_grid_column{j} (row : Basis) : grid (densityAt row {j}) =
    SourceSignedEvaluator.point (densityMatrix row {j}) := by
    fin_cases row
    closeIntegerCells density_grid fixed {j} width 98 transposed 1"

elab "closeIntegerRows " stem:ident " at " arg:term : tactic => withMainContext do
  let value ← Term.elabTerm arg none
  let goals ← getGoals
  unless goals.length == 20 || goals.length == 98 do throwError "complete source row or column census"
  for (goal, i) in goals.zipIdx do
    let name := (← getCurrNamespace) ++ Name.mkSimple s!"{stem.getId.toString}{i}"
    goal.assign (mkApp (Lean.mkConst name) value)
  setGoals []

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerMatrix
