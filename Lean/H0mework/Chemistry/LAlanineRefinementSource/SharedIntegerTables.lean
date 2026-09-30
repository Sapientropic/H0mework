import H0mework.Chemistry.LAlanineRefinementSource.FiniteData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceSharedTables

open Lean Elab Term Command SourceFiniteData
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Inertia.SourceParsing

private def declare (name : Name) (value : Expr) : TermElabM Name := do
  let name := (← getCurrNamespace) ++ name
  let type ← Meta.inferType value
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)
  pure name

/-- Share source rows, so a local contraction does not normalize unrelated source rows. -/
elab "shareSourceIntegerTables" : command => liftTermElabM do
  let packet ← parse SourceFiniteData.sourceText
  let source ← field packet "generated_bounds"
  for (stem, key, height) in [("matrix", "density_matrix_absolute_integer_bounds", 98),
      ("orbital", "orbital_integer_bounds", 35)] do
    let rows ← decode (Array (Array Nat)) (← field source key)
    unless rows.size == height && rows.all (fun row => row.size == 98) do throwError "Source integer table census"
    let mut references : List Expr := []
    for i in [:height] do
      let name ← declare (Name.mkSimple s!"{stem}Row{i}") (toExpr rows[i]!)
      references := references ++ [Lean.mkConst name]
    let value ← Meta.mkArrayLit (mkApp (Lean.mkConst ``Array [.zero]) (Lean.mkConst ``Nat)) references
    discard <| declare (Name.mkSimple s!"{stem}Rows") value

shareSourceIntegerTables

noncomputable def matrix (i j : Basis) : Nat := (matrixRows[i.val]!)[j.val]!
noncomputable def orbital (d : JetIndex) (j : Basis) : Nat := (orbitalRows[d.val]!)[j.val]!

theorem matrix_commutes (i j : Basis) : matrix i j = densityMatrixIntegerBound i j := rfl
theorem orbital_commutes (d : JetIndex) (j : Basis) : orbital d j = orbitalIntegerBound d j := rfl

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceSharedTables
