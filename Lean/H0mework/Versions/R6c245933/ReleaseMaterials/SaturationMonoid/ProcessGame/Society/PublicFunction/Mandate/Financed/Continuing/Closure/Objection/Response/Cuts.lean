import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response

open ResponsibilityLifecycle

variable {fuel : ℚ} {inputs : List (List Action)} {claim : Claim fuel inputs}

def receiveRun (history : History fuel inputs claim) (position : Position fuel inputs) :
    (process fuel inputs claim).Run history.state.current (history.receive fuel inputs position).state.current := by
  cases history with
  | closed state archive slots => exact .nil
  | pending state slots =>
    unfold History.receive
    split
    · exact .nil
    · rename_i attempt selected
      dsimp only
      split
      · exact .step .nil (.cross (P := process fuel inputs claim) ⟨0, by simp [History.state, slots]⟩ (obligation fuel inputs claim)
          (by simp [History.state, slots]) ⟨attempt, rfl⟩)
      · exact .step .nil (.cross (P := process fuel inputs claim) ⟨0, by simp [History.state, slots]⟩ (obligation fuel inputs claim)
          (by simp [History.state, slots]) ⟨attempt, rfl⟩)

def visitRun (history : History fuel inputs claim) (positions : List (Position fuel inputs)) :
    (process fuel inputs claim).Run history.state.current
      (positions.foldl (History.receive fuel inputs) history).state.current := by
  induction positions generalizing history with
  | nil => exact .nil
  | cons position tail ih => exact (receiveRun history position).concatRuns _ (ih (history.receive fuel inputs position))

def fromCut (claim : Claim fuel inputs) (count : Nat) : (later : Nat) →
    (process fuel inputs claim).Run (through fuel inputs claim count).state.current
      (through fuel inputs claim (count + later)).state.current
  | 0 => .nil
  | later + 1 => (fromCut claim count later).concatRuns _
      (visitRun (through fuel inputs claim (count + later)) (positionsAt fuel inputs (count + later)))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response
