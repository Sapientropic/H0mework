import H0mework.Chemistry.LAlanineBandFlowBounds.Common

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.FlowBounds
open WholeBandSource WholeBandReplay WholeBandTransverse WholeBandContinuation
open WholeBandContinuationDifferential WholeBandCell0Differential SourceSignedEvaluator TrueFlowGeometry

open Lean Elab Command

/-- Source replay inputs pay the finite report inequalities once per original row. -/
elab "generateCellFlowBounds " cell:num : command => do
  let c := cell.getNat
  unless 2 ≤ c && c < 32 do throwError "remaining original cell range"
  for k in [:32] do
    let r := 32*c+k
    WholeBandReplay.emit s!"theorem analyticInput{r} : AnalyticBounds input{r} := by
      constructor <;> decide +kernel"
    WholeBandReplay.emit s!"theorem analyticRow{r} : AnalyticBounds (rowInput {c} {k/16} {k%16}) := by
      rw [← input{r}_source]
      exact analyticInput{r}"
    if c != 16 then
      WholeBandReplay.emit s!"theorem positiveInput{r} : 0 < normalInput input{r} := by decide +kernel"
      WholeBandReplay.emit s!"theorem positiveRow{r} : 0 < normalLower (tubeCallAt {c} {k/16} {k%16}) := by
        rw [← normalInput_source, ← input{r}_source]
        exact positiveInput{r}"
  let analytics := String.intercalate "\n" ((List.range 32).map fun k => s!"    · exact analyticRow{32*c+k}")
  WholeBandReplay.emit s!"theorem cell{c}_bounds : CellBounds {c} := by
    intro d i
    fin_cases d <;> fin_cases i
{analytics}"
  if c != 16 then
    let positives := String.intercalate "\n" ((List.range 32).map fun k => s!"    · exact positiveRow{32*c+k}")
    WholeBandReplay.emit s!"theorem cell{c}_positive : PositiveNormalReports {c} := by
    intro d i
    fin_cases d <;> fin_cases i
{positives}"

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.FlowBounds
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
