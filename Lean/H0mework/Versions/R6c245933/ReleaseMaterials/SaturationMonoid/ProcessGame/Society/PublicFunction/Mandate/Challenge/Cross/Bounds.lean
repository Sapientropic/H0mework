import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Transport

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (bound : BoundSource base scope)
  {originInputs inputs : List (RawEvent Party Good Port (State Party Technology) Instrument)}
  {original : Claim (fromHistory bound) originInputs}

private theorem local_reconfirmation_position (claim : Claim (fromHistory bound) inputs) (position : Position (fromHistory bound) inputs)
    (receipt : Challenge.Reconfirmation (Mandate.Challenge.fromHistory bound) inputs claim)
    (decoded : Challenge.readReconfirmation (Mandate.Challenge.fromHistory bound) inputs claim position = some receipt) : receipt.target.position = position := by
  unfold Challenge.readReconfirmation at decoded
  split at decoded
  · cases decoded
  · rename_i target selected
    split at decoded
    · cases Option.some.inj decoded
      exact Challenge.read_position _ _ _ _ selected
    · cases decoded

def localWithin (count : Nat) {claim : Claim (fromHistory bound) inputs} : Challenge.History (Mandate.Challenge.fromHistory bound) inputs claim → Prop
  | .pending target _ _ => (target.claim (fromHistory bound) inputs).position.ordinal < count
  | .closed .. => True

private theorem local_receive_within (count : Nat) {claim : Claim (fromHistory bound) inputs} (history : Challenge.History (Mandate.Challenge.fromHistory bound) inputs claim)
    (position : Position (fromHistory bound) inputs) (prior : localWithin bound count history) (inside : position.ordinal < count) :
    localWithin bound count (history.receive (Mandate.Challenge.fromHistory bound) inputs position) := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots =>
    cases selected : Challenge.readReconfirmation (Mandate.Challenge.fromHistory bound) inputs claim position with
    | some receipt =>
      simp only [Challenge.History.receive, selected]
      split
      · change receipt.target.position.ordinal < count
        rw [local_reconfirmation_position bound _ _ _ selected]
        exact inside
      · exact prior
    | none =>
      cases attempted : readAttempt (fromHistory bound) inputs (target.claim (fromHistory bound) inputs) position with
      | none => simpa only [Challenge.History.receive, selected, attempted] using prior
      | some receipt =>
        simp only [Challenge.History.receive, selected, attempted]
        split
        · exact True.intro
        · exact prior

private theorem local_fold_within (count : Nat) {claim : Claim (fromHistory bound) inputs} (history : Challenge.History (Mandate.Challenge.fromHistory bound) inputs claim)
    (positions : List (Position (fromHistory bound) inputs)) (prior : localWithin bound count history)
    (inside : ∀ position ∈ positions, position.ordinal < count) :
    localWithin bound count (positions.foldl (Challenge.History.receive (Mandate.Challenge.fromHistory bound) inputs) history) := by
  induction positions generalizing history with
  | nil => exact prior
  | cons position tail ih =>
      exact ih (history.receive (Mandate.Challenge.fromHistory bound) inputs position) (local_receive_within bound _ _ _ prior (inside position (by simp)))
        (fun next mem => inside next (by simp [mem]))

theorem local_through_within (claim : Claim (fromHistory bound) inputs) (count limit : Nat)
    (originalInside : claim.position.ordinal < limit) (past : count ≤ limit) :
    localWithin bound limit (Challenge.through (Mandate.Challenge.fromHistory bound) inputs claim count) := by
  induction count with
  | zero => exact originalInside
  | succ count ih =>
      apply local_fold_within bound limit _ _ (ih (by omega))
      intro position member
      obtain ⟨index, _, same⟩ := List.mem_map.mp member
      cases same
      change count < limit
      omega

theorem inherit_within (count : Nat) (history : Challenge.History (Mandate.Challenge.fromHistory bound) originInputs original)
    (prior : localWithin bound count history) : History.Within bound count (History.inherit (fromHistory bound) history) := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots => cases target <;> exact prior

private theorem reconfirmation_position (target : Target (fromHistory bound) original inputs) (position : Position (fromHistory bound) inputs)
    (receipt : Reconfirmation (fromHistory bound) target) (decoded : readReconfirmation (fromHistory bound) target position = some receipt) : receipt.claim.position = position := by
  unfold readReconfirmation at decoded
  split at decoded
  · cases decoded
  · rename_i claim selected
    split at decoded
    · cases Option.some.inj decoded
      exact Challenge.read_position _ _ _ _ selected
    · cases decoded

theorem receive_within (count : Nat) (history : History (fromHistory bound) original inputs) (position : Position (fromHistory bound) inputs)
    (prior : History.Within bound count history) (inside : position.ordinal < count) : History.Within bound count (history.receive (Mandate.Challenge.fromHistory bound) position) := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots =>
    cases selected : readReconfirmation (fromHistory bound) target position with
    | some receipt =>
      simp only [History.receive, selected]
      change receipt.claim.position.ordinal < count
      rw [reconfirmation_position bound _ _ _ selected]
      exact inside
    | none =>
      cases attempted : readAttempt (fromHistory bound) inputs target.claim position with
      | none => simpa only [History.receive, selected, attempted] using prior
      | some receipt =>
        simp only [History.receive, selected, attempted]
        split
        · exact True.intro
        · exact prior

theorem fold_within (count : Nat) (history : History (fromHistory bound) original inputs) (positions : List (Position (fromHistory bound) inputs))
    (prior : History.Within bound count history) (inside : ∀ position ∈ positions, position.ordinal < count) :
    History.Within bound count (positions.foldl (History.receive (fromHistory bound)) history) := by
  induction positions generalizing history with
  | nil => exact prior
  | cons position tail ih =>
      exact ih (history.receive (Mandate.Challenge.fromHistory bound) position) (receive_within bound _ _ _ prior (inside position (by simp)))
        (fun next mem => inside next (by simp [mem]))

theorem transported_within (word : RawEvent Party Good Port (State Party Technology) Instrument) (history : History (fromHistory bound) original inputs)
    (within : History.Within bound (inputs.length + 2) history) :
    History.Within bound ((nextInputs inputs word).length + 2) (transportHistory bound word history within) := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots =>
      change target.claim.position.ordinal < inputs.length + 2 at within
      change (replacement bound inputs word target.claim within).position.ordinal < (nextInputs inputs word).length + 2
      rw [(replacement_same_item_and_snapshot bound inputs word target.claim within).2.2.2.1]
      simp only [nextInputs, List.length_append, List.length_singleton]
      omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross
