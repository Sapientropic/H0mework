import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross.Native
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response.Origin

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {fuel : ℚ} {originInputs inputs : List (List Action)} {original : Claim fuel originInputs}

def transportAnchor (cut : Cut fuel inputs) (word : List Action) (anchor : Anchor original inputs)
    (inside : anchor.image.position.ordinal < cut.depth + 2) : Anchor original (branchInputs cut word) where
  image := Response.replacement cut word anchor.image inside
  ordinal := (Response.replacement_preserves_original_item_and_snapshot cut word anchor.image inside).2.2.1.trans anchor.ordinal
  index := (Response.replacement_preserves_original_item_and_snapshot cut word anchor.image inside).2.2.2.trans anchor.index
  item := (Response.replacement_preserves_original_item_and_snapshot cut word anchor.image inside).1.trans anchor.item
  common := fun ordinal before => (Response.common_items cut word ordinal (by rw [anchor.ordinal] at inside; omega)).trans
    (anchor.common ordinal before)

def transportTarget (cut : Cut fuel inputs) (word : List Action) (target : Target original inputs)
    (inside : target.claim.position.ordinal < cut.depth + 2) : Target original (branchInputs cut word) where
  anchor := transportAnchor cut word target.anchor (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)
  claim := Response.replacement cut word target.claim inside
  afterOrigin := by
    change (Response.replacement cut word target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).position.ordinal <
        (Response.replacement cut word target.claim inside).position.ordinal ∨
      ((Response.replacement cut word target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).position.ordinal =
          (Response.replacement cut word target.claim inside).position.ordinal ∧
        (Response.replacement cut word target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).position.index.val ≤
          (Response.replacement cut word target.claim inside).position.index.val)
    have originOrdinal := (Response.replacement_preserves_original_item_and_snapshot cut word target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).2.2.1
    have targetOrdinal := (Response.replacement_preserves_original_item_and_snapshot cut word target.claim inside).2.2.1
    have originIndex := (Response.replacement_preserves_original_item_and_snapshot cut word target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).2.2.2
    have targetIndex := (Response.replacement_preserves_original_item_and_snapshot cut word target.claim inside).2.2.2
    rcases target.afterOrigin with later | ⟨same, index⟩ <;> omega

theorem transported_target_keeps_snapshot (cut : Cut fuel inputs) (word : List Action) (target : Target original inputs)
    (inside : target.claim.position.ordinal < cut.depth + 2) : (transportTarget cut word target inside).snapshot = target.snapshot :=
  (Response.replacement_preserves_original_item_and_snapshot cut word target.claim inside).2.1

def History.Within (count : Nat) : History original inputs → Prop
  | .pending target _ _ => target.claim.position.ordinal < count
  | .closed .. => True

def transportHistory (cut : Cut fuel inputs) (word : List Action) (history : History original inputs)
    (within : history.Within (cut.depth + 2)) : History original (branchInputs cut word) := by
  cases history with
  | closed state archive slots => exact .closed state archive slots
  | pending target state slots =>
      let next := transportTarget cut word target within
      have same : tracked next = tracked target :=
        congrArg (fun residual : State Bool Unit => { obligation fuel originInputs original with residual := residual })
          (transported_target_keeps_snapshot cut word target within)
      exact .pending next state (slots.trans (congrArg (fun obligation => [ObligationSlot.live obligation]) same).symm)

theorem transport_preserves_the_entire_generated_state (cut : Cut fuel inputs) (word : List Action)
    (history : History original inputs) (within : history.Within (cut.depth + 2)) :
    (transportHistory cut word history within).state = history.state := by cases history <;> rfl

theorem transport_preserves_archived_receipt (cut : Cut fuel inputs) (word : List Action)
    (state : (process original).GeneratedState) (archive : TerminalArchive (V fuel originInputs))
    (slots : state.current.slots = [.terminal archive]) :
    transportHistory cut word (.closed state archive slots) True.intro = .closed state archive slots := rfl

def receiveRun (history : History original inputs) (position : Position fuel inputs) :
    (process original).Run history.state.current (history.receive position).state.current := by
  cases history with
  | closed state archive slots => exact .nil
  | pending target state slots =>
    cases renewed : readReconfirmation target position with
    | some receipt =>
      simp only [History.receive, renewed]
      exact .step .nil (.cross (P := process original) ⟨0, by simp [History.state, slots]⟩
        (tracked target) (by simp [History.state, slots]) (.reaffirm target receipt rfl))
    | none =>
      cases attempted : readAttempt fuel inputs target.claim position with
      | none => simp only [History.receive, renewed, attempted]; exact .nil
      | some receipt =>
        simp only [History.receive, renewed, attempted]
        split
        · exact .step .nil (.cross (P := process original) ⟨0, by simp [History.state, slots]⟩
            (tracked target) (by simp [History.state, slots]) (.attempt target receipt rfl))
        · exact .step .nil (.cross (P := process original) ⟨0, by simp [History.state, slots]⟩
            (tracked target) (by simp [History.state, slots]) (.attempt target receipt rfl))

def visitRun (history : History original inputs) (positions : List (Position fuel inputs)) :
    (process original).Run history.state.current (positions.foldl History.receive history).state.current := by
  induction positions generalizing history with
  | nil => exact .nil
  | cons position tail ih => exact (receiveRun history position).concatRuns _ (ih (history.receive position))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross
