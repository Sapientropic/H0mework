import H0mework.Chemistry.LAlanineWholeCell.SourceData
import H0mework.Chemistry.LAlanineSourceMatrix.MatrixSharedPointColumns

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellMatrix

open Lean Elab Term Command SourceIntegerGrid

private def positiveInteger (input : Expr) : Except String Int := do
  let input := input.consumeMData
  unless input.isAppOfArity ``OfNat.ofNat 3 do throw "source integer literal expected"
  match input.getAppArgs[1]! with
  | .lit (.natVal n) => pure (Int.ofNat n)
  | _ => throw "source integer numeral expected"

private def integer (input : Expr) : Except String Int := do
  let input := input.consumeMData
  if input.isAppOfArity ``Neg.neg 3 then return -(← positiveInteger input.getAppArgs[2]!)
  positiveInteger input

private def pair (input : Expr) : Except String Interval := do
  let input := input.consumeMData
  unless input.isAppOfArity ``Prod.mk 4 do throw "source integer pair expected"
  return (← integer input.getAppArgs[2]!, ← integer input.getAppArgs[3]!)

private def literalList : Nat → Expr → Except String (List Interval)
  | 0, _ => .error "source literal exceeds registered census"
  | fuel + 1, input => do
    let input := input.consumeMData
    if input.isAppOfArity ``List.nil 1 then return []
    unless input.isAppOfArity ``List.cons 3 do throw "source list literal expected"
    return (← pair input.getAppArgs[1]!) :: (← literalList fuel input.getAppArgs[2]!)

private def originalLiteral (name : Name) (count : Nat) (asArray : Bool) : TermElabM (List Interval) := do
  let some (.defnInfo info) := (← getEnv).find? name | throwError "source literal missing {name}"
  unless info.safety == .safe do throwError "unsafe source literal"
  unless ← Meta.isDefEq info.type (if asArray then toTypeExpr (Array Interval) else toTypeExpr (List Interval)) do
    throwError "source literal type"
  let mut value := info.value.consumeMData
  if asArray then
    unless value.isAppOfArity ``List.toArray 2 do throwError "source array is not a native literal"
    value := value.getAppArgs[1]!
  let result ← match literalList (count + 1) value with
    | .ok result => pure result
    | .error message => throwError "{name}: {message}"
  unless result.length == count do throwError "source literal census"
  pure result

private def originalBase : String :=
  "SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement."

elab "generateWholeCellMatrix " number:num : command => liftTermElabM do
  let f := number.getNat
  unless 0 < f && f < 65 do throwError "registered new whole-cell field"
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash SourceFiniteData.sourceText == "704198fc5fb94e27e32ff770d5b1c1e41918fb5aa1fc27a4d8035dba3f499451" &&
      hash WholeCellSource.packetText == WholeCellSource.packetSha256 do
    throwError "original Gaussian or whole-cell source changed"
  let mut originalAO : Array (List Interval) := #[]
  for b in [:98] do
    originalAO := originalAO.push (← originalLiteral
      (originalBase ++ s!"WholeCellCache.Field{f}.aoRow{b}").toName 10 true)
  let ao := (Array.range 10).map fun j => ((Array.range 98).map fun b => (originalAO[b]!)[j]!).toList
  let mut columns : Array (List Interval) := #[]
  for b in [:98] do
    columns := columns.push (← originalLiteral (originalBase ++ s!"SourceIntegerMatrix.density{b}").toName 98 false)
  let first := ao.map fun row => (columns.map fun column => dotList row column).toList
  let bilinear := first.map fun row => (ao.map fun right => dotList row right).toList
  let valid ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit f) (mkNatLit 65))
  WholeCellSource.declareSource `fieldIndex (mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 65) (mkNatLit f) valid)
  for (stem, rows) in [("ao", ao), ("first", first), ("bilinear", bilinear)] do
    for i in [:10] do WholeCellSource.declareSource (Name.mkSimple (stem ++ toString i)) (toExpr rows[i]!)
  for i in [:10] do
    WholeCellSource.declareSource (Name.mkSimple ("aoMid" ++ toString i)) (toExpr ((ao[i]!).map mid))
    WholeCellSource.declareSource (Name.mkSimple ("aoRad" ++ toString i)) (toExpr ((ao[i]!).map rad))

end LAlanine40K2025.BasinRefinement.WholeCellMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
