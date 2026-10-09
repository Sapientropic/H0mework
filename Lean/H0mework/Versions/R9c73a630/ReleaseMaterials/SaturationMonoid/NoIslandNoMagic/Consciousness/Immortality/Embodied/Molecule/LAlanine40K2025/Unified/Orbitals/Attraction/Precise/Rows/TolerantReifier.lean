import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.Reifier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.PreciseReifier
open Lean Elab Term Command
open LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals.SourceReifier

private def finAt (value bound : Nat) : TermElabM Expr := do
  let proof ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit bound))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit bound) (mkNatLit value) proof

elab "generatePreciseAttractionTolerantBlock " row:num start:num stop:num tolerance:num : command =>
    liftTermElabM do
  let b := row.getNat
  let first := start.getNat
  let last := stop.getNat
  let allowed := tolerance.getNat
  unless b < 98 && b ≤ first && first < last && last ≤ 98 && 0 < allowed do
    throwError "precise attraction tolerant upper-triangle block"
  let root ← getCurrNamespace
  let bExpr ← finAt b 98
  let eps := toExpr ((allowed : ℚ)/10^12)
  for c in [first:last] do
    let cExpr ← finAt c 98
    let residualType := mkApp3 (Lean.mkConst ``PreciseResidual) bExpr cExpr eps
    let residualName := root ++ Name.mkSimple s!"vcell{b}_{c}_residual"
    let residualValue ← exactComputation residualType
    let name := residualName
    let type := residualType
    let value := residualValue
    addDecl (.thmDecl {name,levelParams := [],type,value})
    let error ← Meta.mkAppM ``actual_precise_ao_error
      #[bExpr,cExpr,eps,Lean.mkConst residualName]
    let name := root ++ Name.mkSimple s!"vcell{b}_{c}_error"
    let type ← Meta.inferType error
    let value := error
    addDecl (.thmDecl {name,levelParams := [],type,value})

end LAlanine40K2025.UnifiedOrbitals.Attraction.PreciseReifier
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
