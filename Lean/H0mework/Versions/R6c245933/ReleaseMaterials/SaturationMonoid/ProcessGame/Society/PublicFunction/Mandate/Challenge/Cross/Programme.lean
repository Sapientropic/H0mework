import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.ProgrammePrefix

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Programme

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type} (bound : ProgrammeFamily base scope Index)
  {originInputs inputs nextInputs : Index} {original : Claim bound originInputs}


private theorem local_reconfirmation_position (claim : Claim bound inputs) (position : Position bound inputs)
    (receipt : Challenge.Reconfirmation bound inputs claim)
    (decoded : Challenge.readReconfirmation bound inputs claim position = some receipt) : receipt.target.position = position := by
  unfold Challenge.readReconfirmation at decoded
  split at decoded
  · cases decoded
  · rename_i target selected
    split at decoded
    · cases Option.some.inj decoded
      exact Challenge.read_position _ _ _ _ selected
    · cases decoded

def localWithin (count : Nat) {claim : Claim bound inputs} : Challenge.History bound inputs claim → Prop
  | .pending target _ _ => (target.claim bound inputs).position.ordinal < count
  | .closed .. => True

private theorem local_receive_within (count : Nat) {claim : Claim bound inputs} (history : Challenge.History bound inputs claim)
    (position : Position bound inputs) (prior : localWithin bound count history) (inside : position.ordinal < count) :
    localWithin bound count (history.receive bound inputs position) := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots =>
    cases selected : Challenge.readReconfirmation bound inputs claim position with
    | some receipt =>
      simp only [Challenge.History.receive, selected]
      split
      · change receipt.target.position.ordinal < count
        rw [local_reconfirmation_position bound _ _ _ selected]
        exact inside
      · exact prior
    | none =>
      cases attempted : readAttempt bound inputs (target.claim bound inputs) position with
      | none => simpa only [Challenge.History.receive, selected, attempted] using prior
      | some receipt =>
        simp only [Challenge.History.receive, selected, attempted]
        split
        · exact True.intro
        · exact prior

private theorem local_fold_within (count : Nat) {claim : Claim bound inputs} (history : Challenge.History bound inputs claim)
    (positions : List (Position bound inputs)) (prior : localWithin bound count history)
    (inside : ∀ position ∈ positions, position.ordinal < count) :
    localWithin bound count (positions.foldl (Challenge.History.receive bound inputs) history) := by
  induction positions generalizing history with
  | nil => exact prior
  | cons position tail ih =>
      exact ih (history.receive bound inputs position) (local_receive_within bound _ _ _ prior (inside position (by simp)))
        (fun next mem => inside next (by simp [mem]))

theorem local_through_within (claim : Claim bound inputs) (count limit : Nat)
    (originalInside : claim.position.ordinal < limit) (past : count ≤ limit) :
    localWithin bound limit (Challenge.through bound inputs claim count) := by
  induction count with
  | zero => exact originalInside
  | succ count ih =>
      apply local_fold_within bound limit _ _ (ih (by omega))
      intro position member
      obtain ⟨index, _, same⟩ := List.mem_map.mp member
      cases same
      change count < limit
      omega

theorem inherit_within (count : Nat) (history : Challenge.History bound originInputs original)
    (prior : localWithin bound count history) : Within bound count (History.inherit bound history) := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots => cases target <;> exact prior

private theorem reconfirmation_position (target : Target bound original inputs) (position : Position bound inputs)
    (receipt : Reconfirmation bound target) (decoded : readReconfirmation bound target position = some receipt) : receipt.claim.position = position := by
  unfold readReconfirmation at decoded
  split at decoded
  · cases decoded
  · rename_i claim selected
    split at decoded
    · cases Option.some.inj decoded
      exact Challenge.read_position _ _ _ _ selected
    · cases decoded

theorem receive_within (count : Nat) (history : History bound original inputs) (position : Position bound inputs)
    (prior : Within bound count history) (inside : position.ordinal < count) : Within bound count (history.receive bound position) := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots =>
    cases selected : readReconfirmation bound target position with
    | some receipt =>
      simp only [History.receive, selected]
      change receipt.claim.position.ordinal < count
      rw [reconfirmation_position bound _ _ _ selected]
      exact inside
    | none =>
      cases attempted : readAttempt bound inputs target.claim position with
      | none => simpa only [History.receive, selected, attempted] using prior
      | some receipt =>
        simp only [History.receive, selected, attempted]
        split
        · exact True.intro
        · exact prior

theorem fold_within (count : Nat) (history : History bound original inputs) (positions : List (Position bound inputs))
    (prior : Within bound count history) (inside : ∀ position ∈ positions, position.ordinal < count) :
    Within bound count (positions.foldl (History.receive bound) history) := by
  induction positions generalizing history with
  | nil => exact prior
  | cons position tail ih =>
      exact ih (history.receive bound position) (receive_within bound _ _ _ prior (inside position (by simp)))
        (fun next mem => inside next (by simp [mem]))


theorem record_is_its_actual_prefix (count : Nat)
    (record : Sigma fun claim : Claim bound inputs => Challenge.History bound inputs claim)
    (actual : record ∈ Challenge.recordsAt bound inputs count) :
    record.1.position.ordinal < count ∧ record.2 = Challenge.through bound inputs record.1 count := by
  obtain ⟨ordinal, before, member⟩ := List.mem_flatMap.mp actual
  obtain ⟨claim, decoded, same⟩ := List.mem_map.mp member
  cases same
  obtain ⟨position, born, selected⟩ := List.mem_filterMap.mp decoded
  have samePosition := Challenge.read_position bound inputs position claim selected
  obtain ⟨index, _, same⟩ := List.mem_map.mp born
  cases same
  exact ⟨by rw [samePosition]; exact List.mem_range.mp before, rfl⟩

def continueFrom (history : History bound original inputs) (start count : Nat) : History bound original inputs :=
  ((List.range count).map (fun offset => start + offset)).foldl
    (fun prior ordinal => (positionsAt bound inputs ordinal).foldl (History.receive bound) prior) history

def continueRun (history : History bound original inputs) (start count : Nat) :
    (process bound original).Run history.state.current (continueFrom bound history start count).state.current := by
  unfold continueFrom
  generalize ((List.range count).map (fun offset => start + offset)) = visits
  induction visits generalizing history with
  | nil => exact .nil
  | cons visit rest ih =>
      exact (visitRun bound history (positionsAt bound inputs visit)).concatRuns _
        (ih ((positionsAt bound inputs visit).foldl (History.receive bound) history))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Programme
