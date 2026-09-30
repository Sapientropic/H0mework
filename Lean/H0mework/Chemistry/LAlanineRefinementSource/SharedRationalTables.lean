import H0mework.Chemistry.LAlanineRefinementSource.FiniteData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSharedRationalTables

open Lean Elab Term Command SourceFiniteData
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Inertia.SourceParsing

private def declare (name : Name) (value : Expr) : TermElabM Name := do
  let name := (← getCurrNamespace) ++ name
  let type ← Meta.inferType value
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)
  pure name

elab "shareSourceRationalRows" : command => liftTermElabM do
  let packet ← parse SourceFiniteData.sourceText
  let source ← field packet "gaussian_source"
  let rows ← decode (Array Json) (← field source "density_matrix")
  unless rows.size == 98 do throwError "Source rational row census"
  let mut references : List Expr := []
  for i in [:98] do
    let row ← decode (Array Json) rows[i]!
    unless row.size == 98 do throwError "Source rational column census"
    let values ← row.mapM fun item => do
      let pair ← decode (Array Json) item
      unless pair.size == 2 do throwError "Source rational shape"
      let numerator ← decode Int pair[0]!
      let denominator ← decode Nat pair[1]!
      unless denominator > 0 do throwError "Source rational denominator"
      pure (numerator, denominator)
    let name ← declare (Name.mkSimple s!"densityRow{i}") (toExpr values)
    references := references ++ [Lean.mkConst name]
  let pairType := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) (Lean.mkConst ``Int) (Lean.mkConst ``Nat)
  let value ← Meta.mkArrayLit (mkApp (Lean.mkConst ``Array [.zero]) pairType) references
  discard <| declare `densityRows value

shareSourceRationalRows

noncomputable def density (i j : Basis) : ℚ := ratRead ((densityRows[i.val]!)[j.val]!)

theorem density_commutes (i j : Basis) : density i j = densityMatrix i j := rfl

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSharedRationalTables
