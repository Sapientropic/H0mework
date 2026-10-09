import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Reports
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.Tiles
import Lean

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.ReportChecking
open Lean Elab Command

private def emit (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error error => throwError "{error}"
  | .ok command => elabCommand command

private def call (t i : Nat) : Nat := 64*(8*(t/16)+i/4)+32*((t/8)%2)+2*(2*(t%8)+(i/2)%2)+i%2

elab "checkHighJetReports " tile:num first:num last:num : command => do
  let t := tile.getNat
  let start := first.getNat
  let stop := last.getNat
  unless t < 64 && start ≤ stop && stop ≤ 32 do throwError "original tile call range"
  for i in [start:stop] do
    let f := call t i
    emit s!"theorem reportGradient_{f} (a : Fin 3) : HighJet.PairWithin
        ((restrictedField {f}).gradient a) ((WholeBandSource.recordedCallField {f}).gradient a) := by
      fin_cases a <;> decide +kernel"
    emit s!"theorem reportHessian_{f} (a b : Fin 3) : HighJet.PairWithin
        ((restrictedField {f}).hessian a b) ((WholeBandSource.recordedCallField {f}).hessian a b) := by
      fin_cases a <;> fin_cases b <;> decide +kernel"
    emit s!"theorem report_{f} : HighJet.FieldWithin (restrictedField {f}) (WholeBandSource.recordedCallField {f}) :=
      ⟨reportGradient_{f},reportHessian_{f}⟩"

elab "assembleHighJetReports " tile:num : command => do
  let t := tile.getNat
  unless t < 64 do throwError "original tile"
  let branches := String.intercalate "\n" ((List.range 32).map fun i => s!"    · exact report_{call t i}")
  emit s!"theorem all_reports (i : HighJet.Slot) : HighJet.FieldWithin
      (restrictedField (HighJet.tileCall {t} i)) (WholeBandSource.recordedCallField (HighJet.tileCall {t} i)) := by
    fin_cases i
{branches}"

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.ReportChecking
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
