import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.Reifier

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandReplay

open Lean Elab Term Command

elab "checkReplayRows " start:num stop:num : command => do
  let first := start.getNat
  let last := stop.getNat
  unless first ≤ last && last ≤ 1024 do throwError "registered row range"
  for r in [first:last] do
    liftTermElabM (progress s!"source row {r}: arithmetic")
    emit s!"theorem arithmetic{r} : InputArithmetic input{r} {r%16} := by
      constructor <;> decide +kernel"
    emit s!"theorem sourceArithmetic{r} : RowArithmetic {r/32} {r%32/16} {r%16} := by
      change InputArithmetic (rowInput {r/32} {r%32/16} {r%16}) {r%16}
      rw [← input{r}_source]
      exact arithmetic{r}"
    if r%16 > 0 then
      emit s!"theorem sourceAdjacency{r} :
        WholeBandSource.endpointBox {r/32} {r%32/16} {r%16-1} =
          WholeBandSource.initialBox {r/32} {r%32/16} {r%16} := by
        change (rowInput {r/32} {r%32/16} {r%16-1}).endpoint =
          (rowInput {r/32} {r%32/16} {r%16}).initial
        rw [← input{r-1}_source, ← input{r}_source]
        rfl"
    liftTermElabM (progress s!"source row {r}: complete")

elab "assembleReplayCells " start:num stop:num : command => do
  let first := start.getNat
  let last := stop.getNat
  unless first ≤ last && last ≤ 32 do throwError "registered cell range"
  for c in [first:last] do
    let rows := String.intercalate "\n" ((List.range 32).map fun i =>
      s!"      · exact sourceArithmetic{32*c+i}")
    emit s!"theorem cellArithmetic{c} (d : WholeBandSource.Direction) (i : WholeBandSource.Step) :
      RowArithmetic {c} d i := by
      fin_cases d <;> fin_cases i
{rows}"
    let joins := String.intercalate "\n" ((List.range 30).map fun i =>
      s!"      · exact sourceAdjacency{32*c+16*(i/15)+i%15+1}")
    emit s!"theorem cellAdjacency{c} (d : WholeBandSource.Direction) (i : Fin 15) :
      WholeBandSource.endpointBox {c} d i.castSucc = WholeBandSource.initialBox {c} d i.succ := by
      fin_cases d <;> fin_cases i
{joins}"
    emit s!"theorem cellInitial{c} :
      WholeBandSource.initialBox {c} 0 0 = WholeBandSource.initialBox {c} 1 0 := by
      change (rowInput {c} 0 0).initial = (rowInput {c} 1 0).initial
      rw [← input{32*c}_source, ← input{32*c+16}_source]
      rfl"

end LAlanine40K2025.BasinRefinement.WholeBandReplay
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
