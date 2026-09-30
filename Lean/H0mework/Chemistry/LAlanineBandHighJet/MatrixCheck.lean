import H0mework.Chemistry.LAlanineBandHighJet.Matrix
import H0mework.Chemistry.LAlanineBandMatrix.Check

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.MatrixChecking
open Lean Elab Term Command SourceIntegerGrid SourceFieldMatrices

private def fin (value size : Nat) : TermElabM Expr := do
  let proof ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit size))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit size) (mkNatLit value) proof

private def equation (suffix : String) (left right : Expr) : TermElabM Unit := do
  let type ← Meta.mkEq left right
  let value ← Meta.mkEqRefl right
  addDecl (.thmDecl { name := (← getCurrNamespace) ++ Name.mkSimple suffix, levelParams := [], type, value })

private def count : TermElabM Nat := do
  let some n ← Meta.getNatValue? (← Meta.whnf (Lean.mkConst ((← getCurrNamespace) ++ `jetCount))) |
    throwError "source jet count"
  unless n == 20 || n == 35 do throwError "original jet prefixes"
  pure n

private def emit (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error message => throwError "{message}"
  | .ok command => elabCommand command

/-- Independent scalar equations avoid re-expanding the full dense matrix in one proof. -/
elab "checkHighJetMatrixRows " start:num stop:num : command => do
  let n ← liftTermElabM count
  let first := start.getNat
  let last := stop.getNat
  unless first ≤ last && last ≤ n do throwError "source jet range"
  for j in [first:last] do
    liftTermElabM do
      let root ← getCurrNamespace
      let rows := Lean.mkConst (root ++ `matrixRows)
      let left ← fin j n
      let row := fun name => Meta.mkAppM name #[rows,left]
      for (stem,name) in [("matrixAOLength",``Matrix.Rows.ao), ("matrixFirstLength",``Matrix.Rows.first)] do
        equation s!"{stem}_{j}" (← Meta.mkAppM ``List.length #[← row name]) (mkNatLit 98)
      equation s!"matrixMid_{j}" (← row ``Matrix.Rows.mids)
        (← Meta.mkAppM ``List.map #[Lean.mkConst ``mid,← row ``Matrix.Rows.ao])
      equation s!"matrixRad_{j}" (← row ``Matrix.Rows.radii)
        (← Meta.mkAppM ``List.map #[Lean.mkConst ``rad,← row ``Matrix.Rows.ao])
      for b in [:98] do
        let right ← fin b 98
        equation s!"matrixFirst_{j}_{b}" (← Meta.mkAppM ``Matrix.firstAt #[rows,left,right])
          (mkApp3 (Lean.mkConst ``pointDot) (← row ``Matrix.Rows.mids) (← row ``Matrix.Rows.radii)
            (mkApp (Lean.mkConst ``PointColumns.column) right))
        equation s!"matrixAO_{j}_{b}"
          (mkApp (Lean.mkConst ``grid) (← Meta.mkAppM ``Matrix.aoAt #[rows,left,right]))
          (mkApp2 (Lean.mkConst (root ++ `sourceAO)) left right)
    let index := s!"(⟨{j}, by decide +kernel⟩ : Fin jetCount)"
    emit s!"theorem matrixFirstRow{j} (b : SourceFiniteData.Basis) :
      HighJet.Matrix.firstAt matrixRows {index} b = SourceFieldMatrices.pointDot
        (matrixRows.mids {index}) (matrixRows.radii {index}) (SourceFieldMatrices.PointColumns.column b) := by
      fin_cases b
      closeRegisteredCells matrixFirst fixed {j} width 98"
    emit s!"theorem matrixAORow{j} (b : SourceFiniteData.Basis) :
      SourceIntegerGrid.grid (HighJet.Matrix.aoAt matrixRows {index} b) = sourceAO {index} b := by
      fin_cases b
      closeRegisteredCells matrixAO fixed {j} width 98"

elab "assembleHighJetMatrix" : command => do
  let n ← liftTermElabM count
  let branches := fun stem => String.intercalate "\n" ((List.range n).map fun j => s!"    · exact {stem}{j}")
  for (stem,type,proof) in [
      ("matrixAOLength","∀ j, (matrixRows.ao j).length = 98","matrixAOLength_"),
      ("matrixFirstLength","∀ j, (matrixRows.first j).length = 98","matrixFirstLength_"),
      ("matrixMidExact","∀ j, matrixRows.mids j = (matrixRows.ao j).map SourceIntegerGrid.mid","matrixMid_"),
      ("matrixRadExact","∀ j, matrixRows.radii j = (matrixRows.ao j).map SourceIntegerGrid.rad","matrixRad_"),
      ("matrixFirstExact","∀ j b, HighJet.Matrix.firstAt matrixRows j b = SourceFieldMatrices.pointDot (matrixRows.mids j) (matrixRows.radii j) (SourceFieldMatrices.PointColumns.column b)","matrixFirstRow"),
      ("matrixAOExact","∀ j b, SourceIntegerGrid.grid (HighJet.Matrix.aoAt matrixRows j b) = sourceAO j b","matrixAORow")] do
    emit s!"theorem {stem} : {type} := by\n    intro j\n    change Fin {n} at j\n    fin_cases j\n{branches proof}"
  emit "theorem matrixCertificate : HighJet.Matrix.Certificate matrixRows sourceAO :=
    ⟨matrixAOLength,matrixFirstLength,matrixAOExact,matrixMidExact,matrixRadExact,matrixFirstExact⟩"

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.MatrixChecking
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
