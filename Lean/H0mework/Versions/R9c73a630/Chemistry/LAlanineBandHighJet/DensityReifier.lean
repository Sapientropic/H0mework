import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Literals
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Density

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.DensityReification
open Lean Elab Term Command SourceIntegerGrid SourceFiniteData Inertia.SourceParsing

private def emit (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error error => throwError "{error}"
  | .ok command => elabCommand command

private def word (jets : Array (Array Nat)) (ao first : Array (List Interval)) :
    List Nat → Array Nat → Array Nat → Interval
  | [], l, r => dotList first[jets.findIdx? (· == l) |>.getD jets.size]! ao[jets.findIdx? (· == r) |>.getD jets.size]!
  | a :: w, l, r => Calculation.addInteger
      (word jets ao first w (l.modify a (· + 1)) r)
      (word jets ao first w l (r.modify a (· + 1)))

elab "generateHighJetDensity" : command => do
  let (n,scope) ← liftTermElabM do
    let root ← getCurrNamespace
    let some n ← Meta.getNatValue? (← Meta.whnf (Lean.mkConst (root ++ `jetCount))) |
      throwError "source jet count"
    let some scope ← Meta.getNatValue? (← Meta.whnf (Lean.mkConst (root ++ `rawScope))) |
      throwError "source scope"
    unless (scope == 0 && n == 20) || (scope == 1 && n == 35) do throwError "original jet prefixes"
    let gaussian ← parse SourceFiniteData.sourceText
    let jets ← decode (Array (Array Nat)) (← field (← field gaussian "generated_bounds") "multiindices")
    unless jets.size == 35 do throwError "original jet table"
    let mut ao : Array (List Interval) := #[]
    let mut first : Array (List Interval) := #[]
    for j in [:n] do
      ao := ao.push (← Literals.originalLiteral (root ++ Name.mkSimple s!"matrixAO{j}") 98 false)
      first := first.push (← Literals.originalLiteral (root ++ Name.mkSimple s!"matrixFirst{j}") 98 false)
    for j in [:n] do
      let m := jets[j]!
      let w := List.replicate m[0]! 0 ++ List.replicate m[1]! 1 ++ List.replicate m[2]! 2
      WholeCellSource.declareSource (Name.mkSimple s!"densityRow{j}") (toExpr (word jets ao first w #[0,0,0] #[0,0,0]))
    pure (n,scope)
  let vector := "![" ++ String.intercalate ", " ((List.range n).map fun j => s!"densityRow{j}") ++ "]"
  emit s!"noncomputable def densityRows : Fin (HighJet.jetCount {scope}) → SourceIntegerGrid.Interval := {vector}"

elab "checkHighJetDensity" : command => do
  let (n,scope) ← liftTermElabM do
    let root ← getCurrNamespace
    let some n ← Meta.getNatValue? (← Meta.whnf (Lean.mkConst (root ++ `jetCount))) | throwError "source jet count"
    let some scope ← Meta.getNatValue? (← Meta.whnf (Lean.mkConst (root ++ `rawScope))) | throwError "source scope"
    pure (n,scope)
  for j in [:n] do
    emit s!"theorem densityComputed{j} : densityRow{j} =
      HighJet.densityInteger {scope} (HighJet.Matrix.bilinearAt matrixRows) ⟨{j}, by decide +kernel⟩ := by rfl"
  let branches := String.intercalate "\n" ((List.range n).map fun j => s!"    · exact densityComputed{j}")
  emit s!"theorem densityComputed (j : Fin (HighJet.jetCount {scope})) : densityRows j =
    HighJet.densityInteger {scope} (HighJet.Matrix.bilinearAt matrixRows) j := by
    change Fin {n} at j
    fin_cases j
{branches}"

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.DensityReification
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
