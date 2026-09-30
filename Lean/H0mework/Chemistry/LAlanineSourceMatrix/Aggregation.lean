import H0mework.Chemistry.LAlanineSourceMatrix.Certificate

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields

open Lean Elab Tactic Command

elab "closeGeneratedLowRelative " group:num : tactic => do
  let goals ← getGoals
  unless goals.length == 3 do throwError "source axis census"
  let base := (← getCurrNamespace) ++ `Checks
  for (goal,a) in goals.zipIdx do
    goal.assign (Lean.mkConst (base ++ Name.mkSimple s!"relative_{group.getNat}_{a}"))
  setGoals []

elab "closeGeneratedLowPolynomial " group:num : tactic => do
  let goals ← getGoals
  unless goals.length == 27 do throwError "source low polynomial census"
  let base := (← getCurrNamespace) ++ `Checks
  for (goal,i) in goals.zipIdx do
    goal.assign (Lean.mkConst (base ++ Name.mkSimple s!"poly_{group.getNat}_{i/9}_{(i/3)%3}_{i%3}"))
  setGoals []

elab "closeGeneratedLowAORow " basis:num : tactic => do
  let goals ← getGoals
  unless goals.length == 10 do throwError "source low-jet census"
  let base := (← getCurrNamespace) ++ `Checks
  for (goal,j) in goals.zipIdx do
    goal.assign (Lean.mkConst (base ++ Name.mkSimple s!"ao_{basis.getNat}_{j}"))
  setGoals []

elab "closeGeneratedLowGroups " stem:str : tactic => do
  let goals ← getGoals
  unless goals.length == 94 do throwError "complete original group census"
  let base := (← getCurrNamespace).toString
  for (goal,g) in goals.zipIdx do
    goal.assign (Lean.mkConst (base ++ "." ++ stem.getString ++ toString g).toName)
  setGoals []

elab "closeGeneratedLowAOs " jet:term : tactic => withMainContext do
  let goals ← getGoals
  unless goals.length == 98 do throwError "complete original AO census"
  let j ← Term.elabTerm jet none
  let base := (← getCurrNamespace).toString
  for (goal,b) in goals.zipIdx do
    goal.assign (mkApp (Lean.mkConst (base ++ ".aoRowComputed" ++ toString b).toName) j)
  setGoals []

private def fieldAggregationCommand (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error error => throwError error
  | .ok commandSyntax => elabCommand commandSyntax

/-- Finite aggregation of independently checked source rows; this performs no interval arithmetic. -/
elab "assembleLowFieldGroups" : command => do
  for g in [:94] do
    fieldAggregationCommand s!"theorem relativeRow{g} (axis : Fin 3) : cachedRelative {g} axis = sourceRelative {g} axis := by\n  fin_cases axis\n  closeGeneratedLowRelative {g}"
    fieldAggregationCommand s!"theorem polynomialRow{g} (axis power order : Fin 3) : cachedPoly {g} axis power order = sourcePolyFromRelative {g} axis power order := by\n  fin_cases axis <;> fin_cases power <;> fin_cases order\n  closeGeneratedLowPolynomial {g}"

elab "assembleLowFieldAOs" : command => do
  for b in [:98] do
    fieldAggregationCommand s!"theorem aoRowComputed{b} (j : LowJet) : calculatedAO j {b} = sourceAO j {b} := by\n  fin_cases j\n  closeGeneratedLowAORow {b}"

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields
