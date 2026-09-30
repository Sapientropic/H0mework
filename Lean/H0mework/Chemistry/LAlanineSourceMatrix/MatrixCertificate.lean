import H0mework.Chemistry.LAlanineSourceMatrix.MatrixRows

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceField1Matrix

open Lean Elab Term Command SourceIntegerGrid

private def fin (value size : Nat) : TermElabM Expr := do
  let valid ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit size))
  pure (mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit size) (mkNatLit value) valid)

private def certify (suffix : String) (left right : Expr) : TermElabM Unit := do
  let type ← Meta.mkEq left right
  let value ← Meta.mkEqRefl right
  addDecl (.thmDecl { name := (← getCurrNamespace) ++ Name.mkSimple suffix, levelParams := [], type, value })

elab "checkField1MatrixRow " index:num : command => liftTermElabM do
  let i := index.getNat
  unless i < 10 do throwError "source low-jet row"
  let left ← fin i 10
  for j in [:98] do
    let right ← fin j 98
    let actual := mkApp2 (Lean.mkConst ``firstAt) left right
    let computed := mkApp2 (Lean.mkConst ``dotList)
      (mkApp (Lean.mkConst ``aoRow) left) (mkApp (Lean.mkConst ``SourceIntegerMatrix.densityColumn) right)
    certify s!"first_{i}_{j}" actual computed
    let actualAO := mkApp (Lean.mkConst ``grid) (mkApp2 (Lean.mkConst ``aoAt) left right)
    certify s!"ao_{i}_{j}" actualAO (mkApp2 (Lean.mkConst ``SourceFields.Field1.calculatedAO) left right)
  for j in [:10] do
    let right ← fin j 10
    let actual := mkApp2 (Lean.mkConst ``bilinearAt) left right
    let computed := mkApp2 (Lean.mkConst ``dotList)
      (mkApp (Lean.mkConst ``firstRow) left) (mkApp (Lean.mkConst ``aoRow) right)
    certify s!"bilinear_{i}_{j}" actual computed

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceField1Matrix
