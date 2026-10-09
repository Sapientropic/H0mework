import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousMatrix.IntegerDataRows
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousMatrix.Data

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerMatrix

open Lean Elab Term Command SourceIntegerGrid SourceSignedEvaluator SourceFiniteData

private def fin (value size : Nat) : TermElabM Expr := do
  let valid ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit size))
  pure (mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit size) (mkNatLit value) valid)

private def certify (suffix : String) (left right : Expr) : TermElabM Unit := do
  let type ← Meta.mkEq left right
  let value ← Meta.mkEqRefl right
  addDecl (.thmDecl { name := (← getCurrNamespace) ++ Name.mkSimple suffix, levelParams := [], type, value })

elab "checkIntegerReadoutRow " index:num : command => liftTermElabM do
  let i := index.getNat
  unless i < 20 do throwError "source derivative row"
  let left ← fin i 20
  for j in [:98] do
    let right ← fin j 98
    let actualAO := mkApp (Lean.mkConst ``grid) (mkApp2 (Lean.mkConst ``aoAt) left right)
    certify s!"ao_grid_{i}_{j}" actualAO (mkApp2 (Lean.mkConst ``SourceRectangleChecks.calculatedAO) left right)
    let actualFirst := mkApp (Lean.mkConst ``grid) (mkApp2 (Lean.mkConst ``firstAt) left right)
    certify s!"first_grid_{i}_{j}" actualFirst (mkApp2 (Lean.mkConst ``SourceSignedMatrix.calculatedFirst) left right)
  for j in [:20] do
    let right ← fin j 20
    let actual := mkApp (Lean.mkConst ``grid) (mkApp2 (Lean.mkConst ``bilinearAt) left right)
    certify s!"bilinear_grid_{i}_{j}" actual (mkApp2 (Lean.mkConst ``SourceSignedMatrix.calculatedBilinear) left right)

elab "checkIntegerDensityColumn " index:num : command => liftTermElabM do
  let j := index.getNat
  unless j < 98 do throwError "original D3 column"
  let column ← fin j 98
  for i in [:98] do
    let row ← fin i 98
    let actual := mkApp (Lean.mkConst ``grid) (mkApp2 (Lean.mkConst ``densityAt) row column)
    let original := mkApp2 (Lean.mkConst ``densityMatrix) row column
    certify s!"density_grid_{i}_{j}" actual (mkApp (Lean.mkConst ``point) original)

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerMatrix
