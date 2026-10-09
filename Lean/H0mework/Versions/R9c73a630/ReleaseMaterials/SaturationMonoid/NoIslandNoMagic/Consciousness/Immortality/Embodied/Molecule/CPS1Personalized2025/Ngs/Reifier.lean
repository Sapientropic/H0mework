import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs.Types

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs

namespace Reifier
open Lean Elab Term
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest
private def raw : String := include_str "../../../../../../../../../../../../../evidence/second-edition/v2/original/Biomedical/runtime/calculations/cps1-joint-alleles/source/packet.json"
def packetSha : String := "de60281a4eaf701673a929403d135a320b75abc89cf79e7e22adfaed11659013"
private def hash : String := Sha256.hex raw
private def parsed := Json.parse raw
abbrev field {α : Type} [FromJson α] (j : Json) (key : String) : TermElabM α := CPS1Personalized2025.Reifier.field j key
private def packet : TermElabM Json := do
  unless hash == packetSha do throwError "Original Figure S8 packet changed"
  match parsed with | .ok value => pure value | .error error => throwError "{error}"
elab "cps1NgsText%" key:str : term => do
  pure (toExpr (← field (← packet) key.getString : String))
elab "cps1NgsNat%" key:str : term => do
  pure (toExpr (← field (← packet) key.getString : Nat))
elab "cps1NgsBases%" key:str : term => do
  CPS1Personalized2025.Reifier.bases (← field (← packet) key.getString)
elab "cps1NgsRows%" : term => do
  let rows : List Json ← field (← packet) "rows"
  let values ← rows.mapM fun row => do
    Meta.mkAppM ``Allele.mk #[← CPS1Personalized2025.Reifier.bases (← field row "word"),
      toExpr (← field row "reads" : Nat),toExpr (← field row "percentage_hundredths" : Nat),
      toExpr (← field row "printed_class" : String)]
  Meta.mkListLit (Lean.mkConst ``Allele) values
end Reifier

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs
