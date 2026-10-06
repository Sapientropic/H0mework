import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Recorded
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Metric.Charge

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.OriginalMetric.Charge
open BasinRefinement SourceFiniteData
open scoped BigOperators
noncomputable section

def sourceRow (b : Basis) : ℚ := ∑ c : Basis, densityMatrix b c * recordedOverlap b c
def absoluteRow (b : Basis) : ℚ := ∑ c : Basis, |densityMatrix b c|

end
end LAlanine40K2025.UnifiedOrbitals.OriginalMetric.Charge

namespace LAlanine40K2025.UnifiedOrbitals.SourceReifier
open Lean Elab Term Command
open Inertia.SourceParsing
open BasinRefinement SourceFiniteData

elab "generateOriginalChargeRows " first:num last:num : command => liftTermElabM do
  let start := first.getNat
  let stop := last.getNat
  unless start ≤ stop && stop ≤ 98 do throwError "original density rows"
  let source ← field (← parse SourceFiniteData.sourceText) "gaussian_source"
  let density ← (← decode (Array (Array Json)) (← field source "density_matrix")).mapM (·.mapM rational)
  let arrays ← field (← parse recordedText) "arrays"
  let overlap ← (← decode (Array (Array Json)) (← field arrays "target_overlap")).mapM (·.mapM rational)
  let root ← getCurrNamespace
  for b in [start:stop] do
    let charge := (List.range 98).foldl (fun total c => total + (density[b]!)[c]! * (overlap[b]!)[c]!) (0 : ℚ)
    let absolute := (List.range 98).foldl (fun total c => total + |(density[b]!)[c]!|) (0 : ℚ)
    let hb ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit b) (mkNatLit 98))
    let index := mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 98) (mkNatLit b) hb
    for (label,value,source) in [("charge",charge,``OriginalMetric.Charge.sourceRow),
        ("absolute",absolute,``OriginalMetric.Charge.absoluteRow)] do
      let name ← declare (Name.mkSimple s!"{label}{b}") (toExpr value)
      let type ← Meta.mkEq (Lean.mkConst name) (mkApp (Lean.mkConst source) index)
      let proof ← exactComputation type
      addDecl (.thmDecl {
        name := root ++ Name.mkSimple s!"{label}{b}_computed"
        levelParams := []
        type := type
        value := proof })

end LAlanine40K2025.UnifiedOrbitals.SourceReifier
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
