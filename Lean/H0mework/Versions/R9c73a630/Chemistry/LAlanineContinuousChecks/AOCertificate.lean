import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AOCalculatedData
import H0mework.Versions.AB.Chemistry.LAlanineContinuousChecks.GroupAssembly
import H0mework.Versions.AB.Chemistry.LAlanineContinuousGroupCache.Data

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks.AOChecks

open Lean Elab Term Command SourceRectangle SourceSignedEvaluator

private def fin (value width : Nat) : TermElabM Expr := do
  let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit width))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit width) (mkNatLit value) inside

private def certify (suffix : String) (left right : Expr) : TermElabM Unit := do
  let type ← Meta.mkEq left right
  let value ← Meta.mkEqRefl right
  addDecl (.thmDecl { name := (← getCurrNamespace) ++ Name.mkSimple suffix, levelParams := [], type, value })

/-- Kernel-check each cached source composition; the reported table is only a separate equality target. -/
elab "checkCachedAO " index:num : command => liftTermElabM do
  let i := index.getNat
  unless i < 98 do throwError "source AO index"
  let basis ← fin i 98
  for j in [:20] do
    let jet ← fin j 20
    let actual := mkApp2 (Lean.mkConst ``calculatedAO) jet basis
    let source := mkApp4 (Lean.mkConst ``groupCachedOrbital)
      (Lean.mkConst ``SourceGroupCache.cachedExp) (Lean.mkConst ``SourceGroupCache.cachedPoly) basis jet
    certify s!"ao_{i}_{j}_computed" actual source
    certify s!"ao_{i}_{j}_reported" actual (mkApp2 (Lean.mkConst ``reportedAO) jet basis)

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks.AOChecks
