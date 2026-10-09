import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.Types

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery

namespace Reifier
open Lean Elab Term
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest
private def raw : String := include_str "../../../../../../../../../../../../../evidence/second-edition/v2/original/Biomedical/runtime/calculations/cps1-actual-delivery/source/packet.json"
def packetSha : String := "785758affa08e8965c87c58dc79a6c1f56fe1f4dbc03bd8b7e85c2ce5d75a8a6"
private def hash : String := Sha256.hex raw
private def parsed := Json.parse raw
abbrev field {α : Type} [FromJson α] (j : Json) (key : String) : TermElabM α := CPS1Personalized2025.Reifier.field j key
private def packet : TermElabM Json := do
  unless hash == packetSha do throwError "Original actual-delivery packet changed"
  match parsed with | .ok value => pure value | .error error => throwError "{error}"
private def dig (keys : List String) : TermElabM Json := do
  let mut value ← packet
  for key in keys do
    value ← field value key
  pure value
private def keysOf (keys : Array (TSyntax `str)) : List String :=
  keys.map (·.getString) |>.toList
private def readJson {α : Type} [FromJson α] (j : Json) : TermElabM α :=
  match fromJson? j with | .ok v => pure v | .error e => throwError "CPS1 actual delivery source ({j.compress}): {e}"
private def rational (text : String) : TermElabM ℚ := do
  match text.splitOn "/" with
  | [numerator, denominator] =>
    match numerator.toNat?, denominator.toNat? with
    | some num, some den => pure ((num : ℚ) / (den : ℚ))
    | _, _ => throwError "Original rational {text}"
  | _ => CPS1Personalized2025.Reifier.decimal text
elab "cps1DeliveryText%" keys:str* : term => do
  let json ← dig (keysOf keys)
  let value : String ← readJson json
  pure (toExpr value)
elab "cps1DeliveryNat%" keys:str* : term => do
  let json ← dig (keysOf keys)
  let value : Nat ← readJson json
  pure (toExpr value)
elab "cps1DeliveryBool%" keys:str* : term => do
  let json ← dig (keysOf keys)
  let value : Bool ← readJson json
  pure (toExpr value)
elab "cps1DeliveryRat%" keys:str* : term => do
  let json ← dig (keysOf keys)
  let value : String ← readJson json
  pure (toExpr (← rational value))
elab "cps1DeliveryRats%" keys:str* : term => do
  let json ← dig (keysOf keys)
  let value : List String ← readJson json
  pure (toExpr (← value.mapM rational))
elab "cps1DeliveryQuote%" key:str : term => do
  let quotes ← field (← packet) "quotes"
  let quote ← field quotes key.getString
  pure (toExpr (← field quote "text" : String))
end Reifier

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery
