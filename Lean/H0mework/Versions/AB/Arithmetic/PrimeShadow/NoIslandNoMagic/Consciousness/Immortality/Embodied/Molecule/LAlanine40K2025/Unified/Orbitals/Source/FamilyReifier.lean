import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Materials

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.SourceReifier
open Lean Elab Term Command

elab "assembleMetricSquareRoots" : command => liftTermElabM do
  let root ← getCurrNamespace
  let type := Lean.mkConst ``SqrtMaterial
  let law := Lean.mkConst ``SqrtComputed
  let itemType := mkApp2 (Lean.mkConst ``Subtype [.succ .zero]) type law
  let items := (List.range 630).map fun i =>
    mkApp4 (Lean.mkConst ``Subtype.mk [.succ .zero]) type law
      (Lean.mkConst (root ++ Name.mkSimple s!"root{i}"))
      (Lean.mkConst (root ++ Name.mkSimple s!"root{i}_computed"))
  discard <| declare `materials (← Meta.mkArrayLit itemType items)

elab "assembleMetricExponentials" : command => liftTermElabM do
  let root ← getCurrNamespace
  let type := Lean.mkConst ``ExpMaterial
  let law := Lean.mkConst ``ExpComputed
  let itemType := mkApp2 (Lean.mkConst ``Subtype [.succ .zero]) type law
  let items := (List.range 3654).map fun i =>
    mkApp4 (Lean.mkConst ``Subtype.mk [.succ .zero]) type law
      (Lean.mkConst (root ++ Name.mkSimple s!"exp{i}"))
      (Lean.mkConst (root ++ Name.mkSimple s!"exp{i}_computed"))
  discard <| declare `materials (← Meta.mkArrayLit itemType items)

end LAlanine40K2025.UnifiedOrbitals.SourceReifier
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
