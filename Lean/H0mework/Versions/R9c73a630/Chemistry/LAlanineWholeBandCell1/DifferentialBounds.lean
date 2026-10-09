import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell01
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.Bounds

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell1Differential

open WholeBandReplay WholeBandSource WholeBandCell0Differential
open Lean Elab Command

elab "checkCell1AnalyticBounds" : command => do
  for r in [32:64] do
    WholeBandReplay.emit s!"theorem input{r}_analytic : AnalyticBounds input{r} := by
      constructor <;> decide +kernel"
    WholeBandReplay.emit s!"theorem row{r}_analytic : AnalyticBounds (rowInput 1 {(r-32)/16} {r%16}) := by
      rw [← input{r}_source]
      exact input{r}_analytic"

checkCell1AnalyticBounds

elab "assembleCell1AnalyticBounds" : command => do
  let rows := String.intercalate "\n" ((List.range 32).map fun r => s!"    · exact row{r+32}_analytic")
  WholeBandReplay.emit s!"theorem cell1_analytic_bounds (d : Direction) (i : Step) :
    AnalyticBounds (rowInput 1 d i) := by
    fin_cases d <;> fin_cases i
{rows}"

assembleCell1AnalyticBounds

end LAlanine40K2025.BasinRefinement.WholeBandCell1Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
