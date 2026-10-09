import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Overlap

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.SourceReifier
open Lean Elab Term Command

elab "retainOriginalMetricRows" : command => liftTermElabM do
  let root := `SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedOrbitals.OriginalMetric
  let listType := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Summand)
  let arrayType := mkApp (Lean.mkConst ``Array [.zero]) listType
  let mut rows : List Expr := []
  for b in [:98] do
    let row := (List.range 98).map (fun c => Lean.mkConst (root ++ Name.mkSimple s!"entry{b}_{c}_summands"))
    rows := (← Meta.mkArrayLit listType row) :: rows
  discard <| declare `rawSummands (← Meta.mkArrayLit arrayType rows.reverse)

end LAlanine40K2025.UnifiedOrbitals.SourceReifier

namespace LAlanine40K2025.UnifiedOrbitals.OriginalMetric
open BasinRefinement SourceFiniteData
noncomputable section

retainOriginalMetricRows

/-- All 43264 ordered primitive contributions remain available to the root material consumer. -/
def retainedSummands (b c : Basis) : List Summand := (rawSummands[b.val]!)[c.val]!

end
end LAlanine40K2025.UnifiedOrbitals.OriginalMetric
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
