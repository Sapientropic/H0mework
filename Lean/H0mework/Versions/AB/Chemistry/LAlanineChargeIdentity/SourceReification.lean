import H0mework.Versions.AB.Chemistry.LAlanineChargeIdentity.SourceData
import H0mework.Versions.AB.Chemistry.LAlanineBondReadout.SourceParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.SourceReification

open Lean Elab Term Inertia.SourceParsing SourceData

def matrix13 (value : Json) : TermElabM Expr := do
  let rows ← decode (Array (Array Int)) value
  unless rows.size == 13 && rows.all (fun row => row.size == 13) do throwError "Charge matrix census"
  Meta.mkAppM ``matrixRead #[toExpr rows]

def vector13 (value : Json) : TermElabM Expr := do
  let rows ← decode (Array Int) value
  unless rows.size == 13 do throwError "Charge vector census"
  Meta.mkAppM ``vectorRead #[toExpr rows]

def selected13 (value : Json) : TermElabM Expr := do
  let rows ← decode (Array Nat) value
  unless rows.size == 13 && rows.toList.Nodup do throwError "Charge selected row census"
  let mut indices : Array FieldRow := #[]
  for row in rows do
    if inside : row < 4851 then indices := indices.push ⟨row, inside⟩
    else throwError "Charge pivot outside original field"
  Meta.mkAppM ``selectedRead #[toExpr indices]

def fieldBlocks (value : Json) : TermElabM Expr := do
  let blocks ← decode (Array Json) value
  let mut offset := 0
  let mut result : Array (Array (Array Int)) := #[]
  for block in blocks do
    let rows ← decode (Array (Array Int)) (← field block "rows")
    unless (← decode Nat (← field block "first_row")) == offset && rows.size == min 128 (4851 - offset) &&
        (← decode Nat (← field block "row_count")) == rows.size && rows.all (fun row => row.size == 13) do
      throwError "Charge full unit-column block incidence"
    offset := offset + rows.size
    result := result.push rows
  unless offset == 4851 && blocks.size == 38 do throwError "Charge complete unit-column census"
  pure (toExpr result)

def residualBlocks (value : Json) : TermElabM Expr := do
  let blocks ← decode (Array Json) value
  let mut offset := 0
  let mut result : Array (Array Int) := #[]
  for block in blocks do
    let rows ← decode (Array Int) (← field block "rows")
    unless (← decode Nat (← field block "first_row")) == offset && rows.size == min 128 (4851 - offset) &&
        (← decode Nat (← field block "row_count")) == rows.size do throwError "Charge residual block incidence"
    offset := offset + rows.size
    result := result.push rows
  unless offset == 4851 && blocks.size == 38 do throwError "Charge complete residual census"
  pure (toExpr result)

end LAlanine40K2025.ChargeIdentity.SourceReification
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
