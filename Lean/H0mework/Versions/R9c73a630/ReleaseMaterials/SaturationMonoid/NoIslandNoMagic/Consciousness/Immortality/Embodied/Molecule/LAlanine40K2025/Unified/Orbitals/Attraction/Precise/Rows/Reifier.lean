import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Recorded
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Reifier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.PreciseReifier
open Lean Elab Term Command
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals.SourceReifier

private def fin (value bound : Nat) : TermElabM Expr := do
  let proof ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit bound))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit bound) (mkNatLit value) proof

private def declareProof (name : Name) (type value : Expr) : TermElabM Unit :=
  addDecl (.thmDecl {name,levelParams := [],type,value})

/-- The source rows and original report are both evaluated by the kernel;
    the target-frame position is read from Reentry, never from the report. -/
elab "generatePreciseAttractionBlock " row:num start:num stop:num : command => liftTermElabM do
  let b := row.getNat
  let first := start.getNat
  let last := stop.getNat
  unless b < 98 && b ≤ first && first < last && last ≤ 98 do
    throwError "precise attraction upper-triangle block"
  let root ← getCurrNamespace
  let bExpr ← fin b 98
  for c in [first:last] do
    let cExpr ← fin c 98
    let eps := toExpr (1/10^12 : ℚ)
    let residualType := mkApp3 (Lean.mkConst ``PreciseResidual) bExpr cExpr eps
    let residualName := root ++ Name.mkSimple s!"vcell{b}_{c}_residual"
    declareProof residualName residualType (← exactComputation residualType)
    let error ← Meta.mkAppM ``actual_precise_ao_error
      #[bExpr,cExpr,eps,Lean.mkConst residualName]
    declareProof (root ++ Name.mkSimple s!"vcell{b}_{c}_error")
      (← Meta.inferType error) error

end LAlanine40K2025.UnifiedOrbitals.Attraction.PreciseReifier
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
