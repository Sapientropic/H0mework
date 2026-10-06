import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.SourceReifier
open Lean Elab Term Command Inertia.SourceParsing

elab "generateOriginalFrameFirstRow " row:num : command => liftTermElabM do
  let i := row.getNat
  unless i < 98 do throwError "original frame row"
  let arrays ← field (← parse recordedText) "arrays"
  let S ← (← decode (Array (Array Json)) (← field arrays "target_overlap")).mapM (·.mapM rational)
  let X ← (← decode (Array (Array Json)) (← field arrays "target_inverse_root")).mapM (·.mapM rational)
  let root ← getCurrNamespace
  let index := fun (k : Nat) => do
    let h ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit k) (mkNatLit 98))
    pure (mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 98) (mkNatLit k) h)
  let ii ← index i
  for j in [:98] do
    let value := (List.range 98).foldl (fun total k => total+(S[i]!)[k]!*(X[k]!)[j]!) (0 : ℚ)
    let name ← declare (Name.mkSimple s!"product{i}_{j}") (toExpr value)
    let type ← Meta.mkEq (Lean.mkConst name) (mkApp2 (Lean.mkConst ``Frame.firstProduct) ii (← index j))
    let proof ← exactComputation type
    addDecl (.thmDecl {
      name := root ++ Name.mkSimple s!"product{i}_{j}_computed"
      levelParams := []
      type := type
      value := proof })
  let size := (List.range 98).foldl (fun total k => total+|(X[k]!)[i]!|) (0 : ℚ)
  let name ← declare (Name.mkSimple s!"columnSize{i}") (toExpr size)
  let type ← Meta.mkEq (Lean.mkConst name) (mkApp (Lean.mkConst ``Frame.columnSize) ii)
  let proof ← exactComputation type
  addDecl (.thmDecl {
    name := root ++ Name.mkSimple s!"columnSize{i}_computed"
    levelParams := []
    type := type
    value := proof })
  let type ← Meta.mkLE (Lean.mkConst name) (toExpr (40 : ℚ))
  let proof ← exactComputation type
  addDecl (.thmDecl {
    name := root ++ Name.mkSimple s!"columnSize{i}_bound"
    levelParams := []
    type := type
    value := proof })

end LAlanine40K2025.UnifiedOrbitals.SourceReifier
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
