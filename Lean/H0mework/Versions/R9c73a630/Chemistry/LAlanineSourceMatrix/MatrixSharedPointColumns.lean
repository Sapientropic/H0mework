import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceMatrix.MatrixSharedReifier
import H0mework.Chemistry.LAlanineSourceMatrix.MatrixSharedPointDot

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices.PointColumns

open Lean Elab Term Command SourceIntegerGrid SourceFiniteData

generateOriginalDensityScalars

noncomputable def column (b : Basis) : List ℤ :=
  ![d0, d1, d2, d3, d4, d5, d6, d7, d8, d9,
    d10, d11, d12, d13, d14, d15, d16, d17, d18, d19,
    d20, d21, d22, d23, d24, d25, d26, d27, d28, d29,
    d30, d31, d32, d33, d34, d35, d36, d37, d38, d39,
    d40, d41, d42, d43, d44, d45, d46, d47, d48, d49,
    d50, d51, d52, d53, d54, d55, d56, d57, d58, d59,
    d60, d61, d62, d63, d64, d65, d66, d67, d68, d69,
    d70, d71, d72, d73, d74, d75, d76, d77, d78, d79,
    d80, d81, d82, d83, d84, d85, d86, d87, d88, d89,
    d90, d91, d92, d93, d94, d95, d96, d97] b

elab "checkOriginalPointColumns" : command => liftTermElabM do
  for j in [:98] do
    let valid ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit j) (mkNatLit 98))
    let b := mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 98) (mkNatLit j) valid
    let left := mkApp (Lean.mkConst ``pointIntervals) (mkApp (Lean.mkConst ``column) b)
    let right := mkApp (Lean.mkConst ``SourceIntegerMatrix.densityColumn) b
    let type ← Meta.mkEq left right
    let value ← Meta.mkEqRefl right
    addDecl (.thmDecl { name := (← getCurrNamespace) ++ Name.mkSimple s!"pointColumn{j}", levelParams := [], type, value })

checkOriginalPointColumns

open Lean Elab Tactic in
elab "closeOriginalPointColumns" : tactic => do
  let goals ← getGoals
  unless goals.length == 98 do throwError "complete original density column census"
  for (goal,j) in goals.zipIdx do
    goal.assign (Lean.mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"pointColumn{j}"))
  setGoals []

theorem column_commutes (b : Basis) : pointIntervals (column b) = SourceIntegerMatrix.densityColumn b := by
  fin_cases b
  closeOriginalPointColumns

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices.PointColumns
