import H0mework.Chemistry.LAlanineBandMatrix.Reifier
import H0mework.Chemistry.LAlanineSourceMatrix.MatrixSharedAssembly

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandMatrix

open Lean Elab Term Command SourceIntegerGrid SourceFieldMatrices

private def fin (value size : Nat) : TermElabM Expr := do
  let proof ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit size))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit size) (mkNatLit value) proof

private def equation (suffix : String) (left right : Expr) : TermElabM Unit := do
  let type ← Meta.mkEq left right
  let value ← Meta.mkEqRefl right
  addDecl (.thmDecl { name := (← getCurrNamespace) ++ Name.mkSimple suffix, levelParams := [], type, value })

private def progress (message : String) : TermElabM Unit := liftM (m := IO) do
  let output ← IO.getStdout
  output.putStrLn message
  output.flush

private def emit (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error message => throwError "{message}"
  | .ok command => elabCommand command

/-- Primitive kernel equations retain the original fast point-column calculation. -/
elab "checkWholeBandMatrixRows " start:num stop:num : command => do
  let first := start.getNat
  let last := stop.getNat
  unless first ≤ last && last ≤ 10 do throwError "registered low-jet range"
  for j in [first:last] do
    liftTermElabM do
      progress s!"matrix row {j}: primitive checks"
      let root ← getCurrNamespace
      let rows := Lean.mkConst (root ++ `matrixRows)
      let left ← fin j 10
      let row := fun name => mkApp2 (Lean.mkConst name) rows left
      for (stem, name, size) in [("matrixAOLength",``Rows.aoRows,98),
          ("matrixFirstLength",``Rows.firstRows,98), ("matrixBilinearLength",``Rows.bilinearRows,10)] do
        equation s!"{stem}_{j}" (← Meta.mkAppM ``List.length #[row name]) (mkNatLit size)
      equation s!"matrixMid_{j}" (row ``Rows.aoMidRows)
        (← Meta.mkAppM ``List.map #[Lean.mkConst ``mid, row ``Rows.aoRows])
      equation s!"matrixRad_{j}" (row ``Rows.aoRadRows)
        (← Meta.mkAppM ``List.map #[Lean.mkConst ``rad, row ``Rows.aoRows])
      for b in [:98] do
        let right ← fin b 98
        equation s!"matrixFirst_{j}_{b}" (mkApp3 (Lean.mkConst ``firstAt) rows left right)
          (mkApp3 (Lean.mkConst ``pointDot) (row ``Rows.aoMidRows) (row ``Rows.aoRadRows)
            (mkApp (Lean.mkConst ``PointColumns.column) right))
        equation s!"matrixAO_{j}_{b}"
          (mkApp (Lean.mkConst ``grid) (mkApp3 (Lean.mkConst ``aoAt) rows left right))
          (mkApp2 (Lean.mkConst (root ++ `sourceAO)) left right)
      for k in [:10] do
        let right ← fin k 10
        equation s!"matrixBilinear_{j}_{k}" (mkApp3 (Lean.mkConst ``bilinearAt) rows left right)
          (mkApp2 (Lean.mkConst ``dotList) (row ``Rows.firstRows)
            (mkApp2 (Lean.mkConst ``Rows.aoRows) rows right))
      progress s!"matrix row {j}: primitives complete"
    emit s!"theorem matrixFirstRow{j} (b : SourceFiniteData.Basis) :
      WholeBandMatrix.firstAt matrixRows {j} b = SourceFieldMatrices.pointDot
        (matrixRows.aoMidRows {j}) (matrixRows.aoRadRows {j}) (SourceFieldMatrices.PointColumns.column b) := by
      fin_cases b
      closeRegisteredCells matrixFirst fixed {j} width 98"
    emit s!"theorem matrixAORow{j} (b : SourceFiniteData.Basis) :
      SourceIntegerGrid.grid (WholeBandMatrix.aoAt matrixRows {j} b) = sourceAO {j} b := by
      fin_cases b
      closeRegisteredCells matrixAO fixed {j} width 98"
    emit s!"theorem matrixBilinearRow{j} (k : SourceFields.LowJet) :
      WholeBandMatrix.bilinearAt matrixRows {j} k =
        SourceIntegerGrid.dotList (matrixRows.firstRows {j}) (matrixRows.aoRows k) := by
      fin_cases k
      closeRegisteredCells matrixBilinear fixed {j} width 10"
    emit s!"theorem matrixRow{j} : WholeBandMatrix.RowComputed matrixRows sourceAO {j} :=
      WholeBandMatrix.rowComputed_of_points matrixRows sourceAO {j}
        matrixAOLength_{j} matrixFirstLength_{j} matrixBilinearLength_{j}
        matrixAORow{j} matrixMid_{j} matrixRad_{j} matrixFirstRow{j} matrixBilinearRow{j}"

elab "assembleWholeBandMatrix" : command => do
  let branches := String.intercalate "\n" ((List.range 10).map fun j => s!"    · exact matrixRow{j}")
  emit s!"theorem matrixComputed (j : SourceFields.LowJet) :
    WholeBandMatrix.RowComputed matrixRows sourceAO j := by
    fin_cases j
{branches}"
  emit "theorem matrixCertificate : WholeBandMatrix.RowsCertificate matrixRows sourceAO :=
    WholeBandMatrix.rowsCertificate_of_computed matrixRows sourceAO matrixComputed"

end LAlanine40K2025.BasinRefinement.WholeBandMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
