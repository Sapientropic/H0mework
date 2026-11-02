import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeHistory

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService

open ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (inputs : List (RawEvent Party Good Port Technology Instrument))

def advancePrefixRun (index : source.Slot) (depth : Nat) (prior : Prefix source inputs index depth) :
    (process source inputs).Run prior.state (advancePrefix source inputs index depth prior).state := by
  rcases prior with ⟨state, run, shape⟩
  cases shape with
  | live unpaid slots =>
      dsimp only [advancePrefix]
      split <;> exact .step .nil (.cross _ _ _ _)
  | terminal paidDepth paid recorded slots => exact .nil

def fromActualCut (index : source.Slot) (start later : Nat) :
    (process source inputs).Run (historyAt source inputs index start).state
      (historyAt source inputs index (start + later)).state := by
  induction later with
  | zero => exact .nil
  | succ later ih =>
      exact ih.concatRuns _ (advancePrefixRun source inputs index (start + later) _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService
