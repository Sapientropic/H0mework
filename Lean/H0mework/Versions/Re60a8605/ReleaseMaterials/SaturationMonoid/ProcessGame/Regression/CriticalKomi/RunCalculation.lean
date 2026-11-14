import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CalculationRuntime

open SaturationMonoid.ProcessGame.Go.CriticalKomi

def queryDepth {n : Nat} {threshold : Int} {origin frame : SaturationMonoid.ProcessGame.Go.Frame n} :
    DecisionCursor.Context threshold origin frame → Nat
  | .root => 0
  | .white _ _ _ _ _ _ _ up => queryDepth up + 1
  | .black _ _ _ _ _ _ _ up => queryDepth up + 1

def report (visit : CalculationRuntime.Visit) : IO Unit := do
  let bounds := CalculationRuntime.mathematicalAt visit
  IO.println s!"proved mathematical interval=[{bounds.lower},{bounds.upper}]"
  match visit.current with
  | .solved solution => IO.println s!"exact margin={solution.value}; both executable policies delivered"
  | .calculating current =>
      IO.println s!"executable policy bracket=[{current.bracket.lower},{current.bracket.upper}]; query={current.queryThreshold}; midpoint={current.bracket.cut}"
      match current.query with
      | .origin _ => IO.println "pending initial source-bound inquiry"
      | .inspect _ _ context => IO.println s!"pending source query; depth={queryDepth context}"
      | .returning _ _ context => IO.println s!"generated answer propagating; depth={queryDepth context}"

def main : IO Unit := do
  let started ← IO.monoMsNow
  let visit := CalculationRuntime.observe 1
  report visit
  IO.println s!"fixed-seed one-event regression: {(← IO.monoMsNow)-started} ms"
