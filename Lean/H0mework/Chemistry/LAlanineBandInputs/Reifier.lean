import H0mework.Chemistry.LAlanineBandInputs.Packed

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGeneratedInputs

open SourceSignedEvaluator SourceExponential SourceRectangle WholeBandSource WholeBandSaturation
open Lean Elab Term Command Inertia.SourceParsing

private def emit (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error message => throwError "{message}"
  | .ok command => elabCommand command

private def progress (text : String) : CommandElabM Unit := liftTermElabM do
  liftM (m := IO) do
    let output ← IO.getStdout
    output.putStrLn text
    output.flush

private def rational (value : Json) : TermElabM ℚ := do
  let q ← WholeCellSource.sourceRational value
  return (q.1 : ℚ) / q.2

/-- Only original inputs generate the thirteen shared squared-distance values. -/
elab "generateBandInputCalculations " first:num last:num : command => do
  let start := first.getNat
  let stop := last.getNat
  unless start < stop && stop ≤ 2048 do throwError "original input call range"
  let centres ← liftTermElabM do
    let source ← field (← parse SourceFiniteData.sourceText) "gaussian_source"
    (← decode (Array (Array Json)) (← field source "centres")).mapM fun row => row.mapM rational
  unless centres.size == 13 && centres.all (·.size == 3) do throwError "original centre census"
  for f in [start:stop] do
    if f % 64 == 32 && start ≤ f-32 then
      emit s!"noncomputable def row{f} : CalculatedInput := row{f-32}"
    else
      liftTermElabM do
        let coordinates ← coordinateLiterals f
        let reductions ← reductionLiterals f
        let box : Rectangle := fun axis => integerInterval coordinates[axis.val]!
        let radii := centres.map fun centre =>
          let value := squaredRadius box (fun axis => centre[axis.val]!)
          (⌊scale * value.1⌋, ⌈scale * value.2⌉)
        WholeCellSource.declareSource (Name.mkSimple s!"rawBox{f}") (toExpr coordinates)
        WholeCellSource.declareSource (Name.mkSimple s!"rawReductions{f}") (toExpr reductions)
        WholeCellSource.declareSource (Name.mkSimple s!"rawRadii{f}") (toExpr radii)
      emit s!"noncomputable def box{f} : Rectangle := fun a => integerInterval rawBox{f}[a.val]!"
      emit s!"noncomputable def reductions{f} (g : Group) : Nat × Nat := rawReductions{f}[g.val]!"
      emit s!"noncomputable def integerRadii{f} (a : Atom) : IntegerPair := rawRadii{f}[a.val]!"
      emit s!"noncomputable def radii{f} (a : Atom) : Pair := integerInterval (integerRadii{f} a)"
      emit s!"theorem radii{f}_exact : ∀ a : Atom, radii{f} a = squaredRadius box{f} (atomCentre a) := by
        decide +kernel"
      emit s!"theorem reductions{f}_valid : ∀ g : Group,
        IntegerReductions (integerRadial integerRadii{f} g) (reductions{f} g) := by decide +kernel"
      emit s!"theorem saturated{f}_valid : ∀ s : SaturatedGroup,
        IntegerSaturation (integerRadial integerRadii{f} (groupAt s)) (reductions{f} (groupAt s)) := by decide +kernel"
      emit s!"noncomputable def input{f} : InputCalculation box{f} reductions{f} := by
        refine ⟨radii{f}, radii{f}_exact, ?_, ?_⟩
        · intro g
          exact (sharedRadial_integer integerRadii{f} g).symm ▸
            integerReductions_sound _ _ (reductions{f}_valid g)
        · intro s
          exact (sharedRadial_integer integerRadii{f} (groupAt s)).symm ▸
            integerSaturation_sound _ _ (saturated{f}_valid s)"
      emit s!"noncomputable def row{f} : CalculatedInput := ⟨rawBox{f}, rawReductions{f}, input{f}⟩"
    if f % 8 == 7 || f+1 == stop then
      progress s!"original band input calculations: {f+1-start}/{stop-start}"

end LAlanine40K2025.BasinRefinement.WholeBandGeneratedInputs
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
