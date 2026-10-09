import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply.Types

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply

namespace Reifier
open Lean Elab Term
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest
private def raw : String := include_str "../../../../../../../../../../../../../evidence/second-edition/v2/original/Biomedical/runtime/calculations/cps1-physical-supply/source/packet.json"
def packetSha : String := "6be4533e6a08f42d9e97b0cc9de587985927547bc8536263c04023c85efbb5fe"
private def hash : String := Sha256.hex raw
private def parsed := Json.parse raw
abbrev field {α : Type} [FromJson α] (j : Json) (key : String) : TermElabM α := CPS1Personalized2025.Reifier.field j key
private def packet : TermElabM Json := do
  unless hash == packetSha do throwError "Original physical-supply packet changed"
  match parsed with | .ok value => pure value | .error error => throwError "{error}"
private def dig (keys : List String) : TermElabM Json := do
  let mut value ← packet
  for key in keys do
    value ← field value key
  pure value
private def keysOf (keys : Array (TSyntax `str)) : List String :=
  keys.map (·.getString) |>.toList
private def readJson {α : Type} [FromJson α] (j : Json) : TermElabM α :=
  match fromJson? j with | .ok v => pure v | .error e => throwError "CPS1 physical supply source ({j.compress}): {e}"
elab "cps1SupplyText%" keys:str* : term => do
  let json ← dig (keysOf keys)
  let value : String ← readJson json
  pure (toExpr value)
elab "cps1SupplyNat%" keys:str* : term => do
  let json ← dig (keysOf keys)
  let value : Nat ← readJson json
  pure (toExpr value)
elab "cps1SupplyBool%" keys:str* : term => do
  let json ← dig (keysOf keys)
  let value : Bool ← readJson json
  pure (toExpr value)
elab "cps1SupplyRat%" keys:str* : term => do
  let json ← dig (keysOf keys)
  let value : String ← readJson json
  pure (toExpr (← CPS1Personalized2025.Reifier.decimal value))
elab "cps1SupplyQuote%" key:str : term => do
  let quotes ← field (← packet) "quotes"
  let quote ← field quotes key.getString
  pure (toExpr (← field quote "text" : String))
end Reifier

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply
