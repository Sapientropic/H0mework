import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup

open ResponsibilityLifecycle

variable {fuel : ℚ} {inputs : List (List Action)} {original : Claim fuel inputs}

def receiveRun (history : History fuel inputs original) (position : Position fuel inputs) :
    (process fuel inputs original).Run history.state.current (history.receive fuel inputs position).state.current := by
  cases history with
  | closed state archive slots => exact .nil
  | pending target state slots =>
    cases renewed : readReconfirmation fuel inputs original position with
    | some receipt =>
      simp only [History.receive, renewed]
      split
      · rename_i later
        exact .step .nil (.cross (P := process fuel inputs original) ⟨0, by simp [History.state, slots]⟩
          (tracked fuel inputs original target) (by simp [History.state, slots]) (.reaffirm target receipt later rfl))
      · exact .nil
    | none =>
      cases attempted : readAttempt fuel inputs (target.claim fuel inputs) position with
      | none => simp only [History.receive, renewed, attempted]; exact .nil
      | some receipt =>
        simp only [History.receive, renewed, attempted]
        split
        · exact .step .nil (.cross (P := process fuel inputs original) ⟨0, by simp [History.state, slots]⟩
            (tracked fuel inputs original target) (by simp [History.state, slots]) (.attempt target receipt rfl))
        · exact .step .nil (.cross (P := process fuel inputs original) ⟨0, by simp [History.state, slots]⟩
            (tracked fuel inputs original target) (by simp [History.state, slots]) (.attempt target receipt rfl))

def visitRun (history : History fuel inputs original) (positions : List (Position fuel inputs)) :
    (process fuel inputs original).Run history.state.current
      (positions.foldl (History.receive fuel inputs) history).state.current := by
  induction positions generalizing history with
  | nil => exact .nil
  | cons position tail ih => exact (receiveRun history position).concatRuns _ (ih (history.receive fuel inputs position))

def continueFrom (history : History fuel inputs original) (count : Nat) : Nat → History fuel inputs original
  | 0 => history
  | later + 1 => (positionsAt fuel inputs (count + later)).foldl (History.receive fuel inputs) (continueFrom history count later)

def continuationRun (history : History fuel inputs original) (count : Nat) : (later : Nat) →
    (process fuel inputs original).Run history.state.current (continueFrom history count later).state.current
  | 0 => .nil
  | later + 1 => (continuationRun history count later).concatRuns _
      (visitRun (continueFrom history count later) (positionsAt fuel inputs (count + later)))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup
