import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Literals

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.MatrixReification
open Lean Elab Term Command SourceIntegerGrid

private def emit (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error error => throwError "{error}"
  | .ok command => elabCommand command

elab "generateHighJetMatrix" : command => do
  let n ← liftTermElabM do
    let root ← getCurrNamespace
    let some n ← Meta.getNatValue? (← Meta.whnf (Lean.mkConst (root ++ `jetCount))) |
      throwError "source jet count"
    unless n == 20 || n == 35 do throwError "original jet prefixes"
    let mut source : Array (List Interval) := #[]
    for b in [:98] do
      source := source.push (← Literals.originalLiteral (root ++ Name.mkSimple s!"aoRow{b}") n true)
    let ao := (Array.range n).map fun j => ((Array.range 98).map fun b => (source[b]!)[j]!).toList
    let mut columns : Array (List Interval) := #[]
    for b in [:98] do
      let name := (``SourceIntegerMatrix.density0).getPrefix ++ Name.mkSimple s!"density{b}"
      columns := columns.push (← Literals.originalLiteral name 98 false)
    let first := ao.map fun row => (columns.map (dotList row)).toList
    for j in [:n] do
      for (stem,values) in [("matrixAO",ao), ("matrixFirst",first)] do
        WholeCellSource.declareSource (Name.mkSimple s!"{stem}{j}") (toExpr values[j]!)
      WholeCellSource.declareSource (Name.mkSimple s!"matrixMid{j}") (toExpr ((ao[j]!).map mid))
      WholeCellSource.declareSource (Name.mkSimple s!"matrixRad{j}") (toExpr ((ao[j]!).map rad))
    pure n
  let vector := fun stem => "![" ++ String.intercalate ", " ((List.range n).map fun j => s!"{stem}{j}") ++ "]"
  emit s!"noncomputable def matrixRows : HighJet.Matrix.Rows jetCount where
    ao := {vector "matrixAO"}
    mids := {vector "matrixMid"}
    radii := {vector "matrixRad"}
    first := {vector "matrixFirst"}"

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.MatrixReification
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
