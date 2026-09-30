import H0mework.Chemistry.LAlanineBandHighJet.Matrix
import Lean

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.Literals
open Lean Elab Term Command SourceIntegerGrid
private def positiveInteger (input : Expr) : Except String Int := do
  let input := input.consumeMData
  unless input.isAppOfArity ``OfNat.ofNat 3 do throw "integer literal expected"
  match input.getAppArgs[1]! with
  | .lit (.natVal n) => pure (Int.ofNat n)
  | _ => throw "integer numeral expected"

private def integer (input : Expr) : Except String Int := do
  let input := input.consumeMData
  if input.isAppOfArity ``Neg.neg 3 then return -(← positiveInteger input.getAppArgs[2]!)
  positiveInteger input

private def pair (input : Expr) : Except String Interval := do
  let input := input.consumeMData
  unless input.isAppOfArity ``Prod.mk 4 do throw "integer pair expected"
  return (← integer input.getAppArgs[2]!, ← integer input.getAppArgs[3]!)

private def literalList : Nat → Expr → Except String (List Interval)
  | 0, _ => .error "literal exceeds source census"
  | fuel + 1, input => do
    let input := input.consumeMData
    if input.isAppOfArity ``List.nil 1 then return []
    unless input.isAppOfArity ``List.cons 3 do throw "native list literal required"
    return (← pair input.getAppArgs[1]!) :: (← literalList fuel input.getAppArgs[2]!)

def originalLiteral (name : Name) (count : Nat) (asArray : Bool) : TermElabM (List Interval) := do
  let some (.defnInfo info) := (← getEnv).find? name | throwError "source literal missing {name}"
  unless info.safety == .safe do throwError "unsafe source literal"
  unless ← Meta.isDefEq info.type (if asArray then toTypeExpr (Array Interval) else toTypeExpr (List Interval)) do
    throwError "source literal type"
  let mut value := info.value.consumeMData
  if asArray then
    unless value.isAppOfArity ``List.toArray 2 do throwError "native array literal required"
    value := value.getAppArgs[1]!
  let result ← match literalList (count + 1) value with
    | .ok result => pure result
    | .error message => throwError "{name}: {message}"
  unless result.length == count do throwError "complete literal census"
  pure result

private def declare (suffix : Name) (value : Expr) : TermElabM Unit :=
  WholeCellSource.declareSource suffix value

private def emit (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error message => throwError "{message}"
  | .ok command => elabCommand command


end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.Literals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
