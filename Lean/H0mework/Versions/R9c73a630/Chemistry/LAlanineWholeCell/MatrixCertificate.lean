import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.MatrixReifier

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellMatrix

open Lean Elab Term Command SourceIntegerGrid SourceFieldMatrices

private def fin (value size : Nat) : TermElabM Expr := do
  let valid ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit size))
  pure (mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit size) (mkNatLit value) valid)

private def certify (suffix : String) (left right : Expr) : TermElabM Unit := do
  let type ← Meta.mkEq left right
  let value ← Meta.mkEqRefl right
  addDecl (.thmDecl { name := (← getCurrNamespace) ++ Name.mkSimple suffix, levelParams := [], type, value })

elab "checkWholeCellMatrixRow " number:num : command => liftTermElabM do
  let i := number.getNat
  unless i < 10 do throwError "whole-cell low-jet row"
  let current ← getCurrNamespace
  let own := fun suffix => Lean.mkConst (current ++ Name.mkSimple suffix)
  let left ← fin i 10
  let midSource ← Meta.mkAppM ``List.map #[Lean.mkConst ``mid, mkApp (own "aoRow") left]
  let radSource ← Meta.mkAppM ``List.map #[Lean.mkConst ``rad, mkApp (own "aoRow") left]
  certify s!"mid_{i}" (mkApp (own "aoMidRow") left) midSource
  certify s!"rad_{i}" (mkApp (own "aoRadRow") left) radSource
  for j in [:98] do
    let right ← fin j 98
    certify s!"firstFast_{i}_{j}" (mkApp2 (own "firstAt") left right)
      (mkApp3 (Lean.mkConst ``pointDot) (mkApp (own "aoMidRow") left) (mkApp (own "aoRadRow") left)
        (mkApp (Lean.mkConst ``PointColumns.column) right))
    certify s!"ao_{i}_{j}" (mkApp (Lean.mkConst ``grid) (mkApp2 (own "aoAt") left right))
      (mkApp2 (own "sourceAO") left right)
  for j in [:10] do
    let right ← fin j 10
    certify s!"bilinear_{i}_{j}" (mkApp2 (own "bilinearAt") left right)
      (mkApp2 (Lean.mkConst ``dotList) (mkApp (own "firstRow") left) (mkApp (own "aoRow") right))

end LAlanine40K2025.BasinRefinement.WholeCellMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
