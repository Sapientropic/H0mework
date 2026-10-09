import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceMatrix.Complete
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousMatrix.IntegerDataComplete

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices

open Lean Elab Term Command SourceIntegerGrid SourceFields SourceFiniteData SourceRectangle

private def positiveIntLiteral (input : Expr) : Except String Int := do
  let input := input.consumeMData
  unless input.isAppOfArity ``OfNat.ofNat 3 do throw "original integer literal expected"
  match input.getAppArgs[1]! with
  | .lit (.natVal n) => pure (Int.ofNat n)
  | _ => throw "original integer numeral expected"

private def intLiteral (input : Expr) : Except String Int := do
  let input := input.consumeMData
  if input.isAppOfArity ``Neg.neg 3 then return -(← positiveIntLiteral input.getAppArgs[2]!)
  positiveIntLiteral input

private def pairLiteral (input : Expr) : Except String Interval := do
  let input := input.consumeMData
  unless input.isAppOfArity ``Prod.mk 4 do throw "original integer pair expected"
  return (← intLiteral input.getAppArgs[2]!, ← intLiteral input.getAppArgs[3]!)

private def listLiteral : Nat → Expr → Except String (List Interval)
  | 0, _ => .error "original finite literal census exhausted"
  | fuel + 1, input => do
    let input := input.consumeMData
    if input.isAppOfArity ``List.nil 1 then return []
    unless input.isAppOfArity ``List.cons 3 do throw "original list literal expected"
    return (← pairLiteral input.getAppArgs[1]!) :: (← listLiteral fuel input.getAppArgs[2]!)

private def originalLiteral (name : Name) (count : Nat) (asArray : Bool) : TermElabM (List Interval) := do
  let some (.defnInfo info) := (← getEnv).find? name | throwError "missing original source literal {name}"
  unless info.safety == .safe do throwError "source literal is unsafe"
  let expected := if asArray then toTypeExpr (Array Interval) else toTypeExpr (List Interval)
  unless ← Meta.isDefEq info.type expected do throwError "original literal type changed"
  let mut value := info.value.consumeMData
  if asArray then
    unless value.isAppOfArity ``List.toArray 2 do throwError "original source array literal changed"
    value := value.getAppArgs[1]!
  let result ← match listLiteral (count + 1) value with
    | .ok result => pure result
    | .error message => throwError "{name}: {message}"
  unless result.length == count do throwError "original literal count changed"
  pure result

private def declare (suffix : String) (value : Expr) : TermElabM Unit := do
  let name := (← getCurrNamespace) ++ Name.mkSimple suffix
  let type ← Meta.inferType value
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

private def originalBase : String :=
  "SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement."

/-- Read only the already-generated native AO/D3 literals; no result JSON or source field report is used. -/
elab "generateRegisteredFieldMatrix " fieldNumber:num : command => liftTermElabM do
  let f := fieldNumber.getNat
  unless 2 ≤ f && f < 17 do throwError "registered remaining field index"
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash SourceFiniteData.sourceText == "704198fc5fb94e27e32ff770d5b1c1e41918fb5aa1fc27a4d8035dba3f499451" &&
      hash SourceRectangle.fieldText == "a366023f2256f1e53c045b6fe9ae951b78876fca4679d7b3ead3e7ca9167c011" do
    throwError "original Gaussian and seventeen-field source changed"
  let mut originalAO : Array (List Interval) := #[]
  for b in [:98] do
    originalAO := originalAO.push (← originalLiteral
      (originalBase ++ s!"SourceFields.Field{f}.aoRow{b}").toName 10 true)
  let ao := (Array.range 10).map fun j => ((Array.range 98).map fun b => (originalAO[b]!)[j]!).toList
  let mut columns : Array (List Interval) := #[]
  for b in [:98] do
    columns := columns.push (← originalLiteral
      (originalBase ++ s!"SourceIntegerMatrix.density{b}").toName 98 false)
  let first := ao.map fun row => (columns.map fun column => dotList row column).toList
  let bilinear := first.map fun row => (ao.map fun right => dotList row right).toList
  let valid ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit f) (mkNatLit 17))
  declare "fieldIndex" (mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 17) (mkNatLit f) valid)
  for (stem, rows) in [("ao", ao), ("first", first), ("bilinear", bilinear)] do
    for i in [:10] do declare (stem ++ toString i) (toExpr rows[i]!)
  for i in [:10] do
    declare ("aoMid" ++ toString i) (toExpr ((ao[i]!).map mid))
    declare ("aoRad" ++ toString i) (toExpr ((ao[i]!).map rad))

elab "generateOriginalDensityScalars" : command => liftTermElabM do
  for b in [:98] do
    let column ← originalLiteral (originalBase ++ s!"SourceIntegerMatrix.density{b}").toName 98 false
    unless column.all (fun entry => entry.1 == entry.2) do throwError "original D3 column is not point-valued"
    declare ("d" ++ toString b) (toExpr (column.map Prod.fst))

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices
