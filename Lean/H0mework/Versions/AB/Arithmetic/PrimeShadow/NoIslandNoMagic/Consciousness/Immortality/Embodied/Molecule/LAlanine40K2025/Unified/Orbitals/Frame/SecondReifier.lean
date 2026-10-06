import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.First.Assembly
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Reifier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData OriginalMetric
open scoped BigOperators
noncomputable section

def secondProduct (i j : Basis) : ℚ := ∑ k : Basis, recordedInverse k i * First.retainedProduct k j

end
end LAlanine40K2025.UnifiedOrbitals.Frame

namespace LAlanine40K2025.UnifiedOrbitals.SourceReifier
open Lean Elab Term Command Inertia.SourceParsing

elab "generateOriginalFrameSecondRow " row:num : command => liftTermElabM do
  let i := row.getNat
  unless i < 98 do throwError "original frame row"
  let arrays ← field (← parse recordedText) "arrays"
  let X ← (← decode (Array (Array Json)) (← field arrays "target_inverse_root")).mapM (·.mapM rational)
  let sourceNamespace := `SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedOrbitals.Frame.First
  let root ← getCurrNamespace
  let index := fun (k : Nat) => do
    let h ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit k) (mkNatLit 98))
    pure (mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 98) (mkNatLit k) h)
  let ii ← index i
  for j in [:98] do
    let mut value : ℚ := 0
    for k in [:98] do
      let name := sourceNamespace ++ Name.mkSimple s!"product{k}_{j}"
      let some (.defnInfo info) := (← getEnv).find? name | throwError "missing original first product {name}"
      let some q ← Meta.getRatValue? info.value | throwError "first product literal {name}"
      value := value+(X[k]!)[i]!*q
    let name ← declare (Name.mkSimple s!"gram{i}_{j}") (toExpr value)
    let type ← Meta.mkEq (Lean.mkConst name) (mkApp2 (Lean.mkConst ``Frame.secondProduct) ii (← index j))
    let proof ← exactComputation type
    addDecl (.thmDecl {
      name := root ++ Name.mkSimple s!"gram{i}_{j}_computed"
      levelParams := []
      type := type
      value := proof })
    let error := |value-(if i == j then 1 else 0)|
    let type ← Meta.mkLE (toExpr error) (toExpr (1/10^10 : ℚ))
    let proof ← exactComputation type
    addDecl (.thmDecl {
      name := root ++ Name.mkSimple s!"gram{i}_{j}_bound"
      levelParams := []
      type := type
      value := proof })

end LAlanine40K2025.UnifiedOrbitals.SourceReifier
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
