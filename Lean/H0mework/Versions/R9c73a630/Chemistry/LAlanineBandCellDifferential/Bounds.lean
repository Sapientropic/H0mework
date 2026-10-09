import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell00

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open WholeBandReplay WholeBandSource SourceSignedEvaluator ContinuousChart

def AnalyticBounds (r : Inputs) : Prop :=
  (∀ axis : Fin 3, (∑ j : Fin 3, magnitude (r.tubeField.hessian axis j)) ≤ (17/20 : ℚ)) ∧
  (∀ axis : Fin 3,
    SourceFiniteData.boxCentre axis - SourceFiniteData.boxRadius + 1/200 < (r.tube axis).1 ∧
    (r.tube axis).2 < SourceFiniteData.boxCentre axis + SourceFiniteData.boxRadius - 1/200)

open Lean Elab Command

elab "checkCell0AnalyticBounds" : command => do
  for r in [:32] do
    WholeBandReplay.emit s!"theorem input{r}_analytic : AnalyticBounds input{r} := by
      constructor <;> decide +kernel"
    WholeBandReplay.emit s!"theorem row{r}_analytic : AnalyticBounds (rowInput 0 {r/16} {r%16}) := by
      rw [← input{r}_source]
      exact input{r}_analytic"

checkCell0AnalyticBounds

elab "assembleCell0AnalyticBounds" : command => do
  let rows := String.intercalate "\n" ((List.range 32).map fun r => s!"    · exact row{r}_analytic")
  WholeBandReplay.emit s!"theorem cell0_analytic_bounds (d : Direction) (i : Step) :
    AnalyticBounds (rowInput 0 d i) := by
    fin_cases d <;> fin_cases i
{rows}"

assembleCell0AnalyticBounds

end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
