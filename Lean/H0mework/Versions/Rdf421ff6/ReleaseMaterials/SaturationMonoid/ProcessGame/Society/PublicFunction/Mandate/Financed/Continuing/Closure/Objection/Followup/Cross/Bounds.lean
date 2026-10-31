import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross.Transport

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {fuel : ℚ} {originInputs inputs : List (List Action)} {original : Claim fuel originInputs}

private theorem local_reconfirmation_position (claim : Claim fuel inputs) (position : Position fuel inputs)
    (receipt : Followup.Reconfirmation fuel inputs claim)
    (decoded : Followup.readReconfirmation fuel inputs claim position = some receipt) : receipt.target.position = position := by
  unfold Followup.readReconfirmation at decoded
  split at decoded
  · cases decoded
  · rename_i target selected
    split at decoded
    · cases Option.some.inj decoded
      exact Response.read_position _ _ selected
    · cases decoded

def localWithin (count : Nat) {claim : Claim fuel inputs} : Followup.History fuel inputs claim → Prop
  | .pending target _ _ => (target.claim fuel inputs).position.ordinal < count
  | .closed .. => True

private theorem local_receive_within (count : Nat) {claim : Claim fuel inputs} (history : Followup.History fuel inputs claim)
    (position : Position fuel inputs) (prior : localWithin count history) (inside : position.ordinal < count) :
    localWithin count (history.receive fuel inputs position) := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots =>
    cases selected : Followup.readReconfirmation fuel inputs claim position with
    | some receipt =>
      simp only [Followup.History.receive, selected]
      split
      · change receipt.target.position.ordinal < count
        rw [local_reconfirmation_position _ _ _ selected]
        exact inside
      · exact prior
    | none =>
      cases attempted : readAttempt fuel inputs (target.claim fuel inputs) position with
      | none => simpa only [Followup.History.receive, selected, attempted] using prior
      | some receipt =>
        simp only [Followup.History.receive, selected, attempted]
        split
        · exact True.intro
        · exact prior

private theorem local_fold_within (count : Nat) {claim : Claim fuel inputs} (history : Followup.History fuel inputs claim)
    (positions : List (Position fuel inputs)) (prior : localWithin count history)
    (inside : ∀ position ∈ positions, position.ordinal < count) :
    localWithin count (positions.foldl (Followup.History.receive fuel inputs) history) := by
  induction positions generalizing history with
  | nil => exact prior
  | cons position tail ih =>
      exact ih (history.receive fuel inputs position) (local_receive_within _ _ _ prior (inside position (by simp)))
        (fun next mem => inside next (by simp [mem]))

theorem local_through_within (claim : Claim fuel inputs) (count bound : Nat)
    (originalInside : claim.position.ordinal < bound) (past : count ≤ bound) :
    localWithin bound (Followup.through fuel inputs claim count) := by
  induction count with
  | zero => exact originalInside
  | succ count ih =>
      apply local_fold_within bound _ _ (ih (by omega))
      intro position member
      obtain ⟨index, _, same⟩ := List.mem_map.mp member
      cases same
      change count < bound
      omega

theorem inherit_within (count : Nat) (history : Followup.History fuel originInputs original)
    (prior : localWithin count history) : (History.inherit history).Within count := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots => cases target <;> exact prior

private theorem reconfirmation_position (target : Target original inputs) (position : Position fuel inputs)
    (receipt : Reconfirmation target) (decoded : readReconfirmation target position = some receipt) : receipt.claim.position = position := by
  unfold readReconfirmation at decoded
  split at decoded
  · cases decoded
  · rename_i claim selected
    split at decoded
    · cases Option.some.inj decoded
      exact Response.read_position _ _ selected
    · cases decoded

theorem receive_within (count : Nat) (history : History original inputs) (position : Position fuel inputs)
    (prior : history.Within count) (inside : position.ordinal < count) : (history.receive position).Within count := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots =>
    cases selected : readReconfirmation target position with
    | some receipt =>
      simp only [History.receive, selected]
      change receipt.claim.position.ordinal < count
      rw [reconfirmation_position _ _ _ selected]
      exact inside
    | none =>
      cases attempted : readAttempt fuel inputs target.claim position with
      | none => simpa only [History.receive, selected, attempted] using prior
      | some receipt =>
        simp only [History.receive, selected, attempted]
        split
        · exact True.intro
        · exact prior

theorem fold_within (count : Nat) (history : History original inputs) (positions : List (Position fuel inputs))
    (prior : history.Within count) (inside : ∀ position ∈ positions, position.ordinal < count) :
    (positions.foldl History.receive history).Within count := by
  induction positions generalizing history with
  | nil => exact prior
  | cons position tail ih =>
      exact ih (history.receive position) (receive_within _ _ _ prior (inside position (by simp)))
        (fun next mem => inside next (by simp [mem]))

theorem transported_within (cut : Cut fuel inputs) (word : List Action) (history : History original inputs)
    (within : history.Within (cut.depth + 2)) :
    (transportHistory cut word history within).Within ((afterInput cut word).depth + 2) := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots =>
      change target.claim.position.ordinal < cut.depth + 2 at within
      change (Response.replacement cut word target.claim within).position.ordinal < (afterInput cut word).depth + 2
      rw [(Response.replacement_preserves_original_item_and_snapshot cut word target.claim within).2.2.1]
      change target.claim.position.ordinal < (branchInputs cut word).length + 2
      rw [branchInputs_length]
      omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross
