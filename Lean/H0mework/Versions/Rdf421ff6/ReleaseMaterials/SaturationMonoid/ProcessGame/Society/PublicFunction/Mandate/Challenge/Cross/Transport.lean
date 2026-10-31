import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (bound : BoundSource base scope)
  {originInputs inputs : List (RawEvent Party Good Port (State Party Technology) Instrument)}
  {original : Claim (fromHistory bound) originInputs}

def transportAnchor (word : RawEvent Party Good Port (State Party Technology) Instrument) (anchor : Anchor (fromHistory bound) original inputs)
    (inside : anchor.image.position.ordinal < inputs.length + 2) : Anchor (fromHistory bound) original (nextInputs inputs word) where
  image := replacement bound inputs word anchor.image inside
  ordinal := (replacement_same_item_and_snapshot bound inputs word anchor.image inside).2.2.2.1.trans anchor.ordinal
  index := (replacement_same_item_and_snapshot bound inputs word anchor.image inside).2.2.2.2.trans anchor.index
  item := (replacement_same_item_and_snapshot bound inputs word anchor.image inside).1.trans anchor.item
  common := fun ordinal before => (common_items bound inputs word ordinal (by rw [anchor.ordinal] at inside; omega)).trans
    (anchor.common ordinal before)

def transportTarget (word : RawEvent Party Good Port (State Party Technology) Instrument) (target : Target (fromHistory bound) original inputs)
    (inside : target.claim.position.ordinal < inputs.length + 2) : Target (fromHistory bound) original (nextInputs inputs word) where
  anchor := transportAnchor bound word target.anchor (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)
  claim := replacement bound inputs word target.claim inside
  afterOrigin := by
    change (replacement bound inputs word target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).position.ordinal <
        (replacement bound inputs word target.claim inside).position.ordinal ∨
      ((replacement bound inputs word target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).position.ordinal =
          (replacement bound inputs word target.claim inside).position.ordinal ∧
        (replacement bound inputs word target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).position.index.val ≤
          (replacement bound inputs word target.claim inside).position.index.val)
    have originOrdinal := (replacement_same_item_and_snapshot bound inputs word target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).2.2.2.1
    have targetOrdinal := (replacement_same_item_and_snapshot bound inputs word target.claim inside).2.2.2.1
    have originIndex := (replacement_same_item_and_snapshot bound inputs word target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).2.2.2
    have targetIndex := (replacement_same_item_and_snapshot bound inputs word target.claim inside).2.2.2.2
    rcases target.afterOrigin with later | ⟨same, index⟩ <;> omega

  signer := (replacement_same_item_and_snapshot bound inputs word target.claim inside).2.2.1.trans
    (target.signer.trans (replacement_same_item_and_snapshot bound inputs word target.anchor.image
      (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).2.2.1.symm)

theorem transported_target_keeps_snapshot (word : RawEvent Party Good Port (State Party Technology) Instrument) (target : Target (fromHistory bound) original inputs)
    (inside : target.claim.position.ordinal < inputs.length + 2) : (transportTarget bound word target inside).snapshot (fromHistory bound) = target.snapshot (fromHistory bound) :=
  (replacement_same_item_and_snapshot bound inputs word target.claim inside).2.1

def History.Within (count : Nat) : History (fromHistory bound) original inputs → Prop
  | .pending target _ _ => target.claim.position.ordinal < count
  | .closed .. => True

def transportHistory (word : RawEvent Party Good Port (State Party Technology) Instrument) (history : History (fromHistory bound) original inputs)
    (within : History.Within bound (inputs.length + 2) history) : History (fromHistory bound) original (nextInputs inputs word) := by
  cases history with
  | closed state archive slots => exact .closed state archive slots
  | pending target state slots =>
      let next := transportTarget bound word target within
      have same : tracked (fromHistory bound) next = tracked (fromHistory bound) target :=
        congrArg (fun residual : State Party Technology => { obligation (fromHistory bound) originInputs original with residual := residual })
          (transported_target_keeps_snapshot bound word target within)
      exact .pending next state (slots.trans (congrArg (fun obligation => [ObligationSlot.live obligation]) same).symm)

theorem transport_preserves_the_entire_generated_state (word : RawEvent Party Good Port (State Party Technology) Instrument)
    (history : History (fromHistory bound) original inputs) (within : History.Within bound (inputs.length + 2) history) :
    (transportHistory bound word history within).state = history.state := by cases history <;> rfl

theorem transport_preserves_archived_receipt (word : RawEvent Party Good Port (State Party Technology) Instrument)
    (state : (process (fromHistory bound) original).GeneratedState) (archive : TerminalArchive (V (fromHistory bound) originInputs))
    (slots : state.current.slots = [.terminal archive]) :
    transportHistory bound (inputs := inputs) word (.closed state archive slots) True.intro = .closed state archive slots := rfl

def receiveRun (history : History (fromHistory bound) original inputs) (position : Position (fromHistory bound) inputs) :
    (process (fromHistory bound) original).Run history.state.current (history.receive (Mandate.Challenge.fromHistory bound) position).state.current := by
  cases history with
  | closed state archive slots => exact .nil
  | pending target state slots =>
    cases renewed : readReconfirmation (fromHistory bound) target position with
    | some receipt =>
      simp only [History.receive, renewed]
      exact .step .nil (.cross (P := process (fromHistory bound) original) ⟨0, by simp [History.state, slots]⟩
        (tracked (fromHistory bound) target) (by simp [History.state, slots]) (.reaffirm target receipt rfl))
    | none =>
      cases attempted : readAttempt (fromHistory bound) inputs target.claim position with
      | none => simp only [History.receive, renewed, attempted]; exact .nil
      | some receipt =>
        simp only [History.receive, renewed, attempted]
        split
        · exact .step .nil (.cross (P := process (fromHistory bound) original) ⟨0, by simp [History.state, slots]⟩
            (tracked (fromHistory bound) target) (by simp [History.state, slots]) (.attempt target receipt rfl))
        · exact .step .nil (.cross (P := process (fromHistory bound) original) ⟨0, by simp [History.state, slots]⟩
            (tracked (fromHistory bound) target) (by simp [History.state, slots]) (.attempt target receipt rfl))

def visitRun (history : History (fromHistory bound) original inputs) (positions : List (Position (fromHistory bound) inputs)) :
    (process (fromHistory bound) original).Run history.state.current (positions.foldl (History.receive (fromHistory bound)) history).state.current := by
  induction positions generalizing history with
  | nil => exact .nil
  | cons position tail ih => exact (receiveRun bound history position).concatRuns _ (ih (history.receive (Mandate.Challenge.fromHistory bound) position))

theorem remote_fulfilled_receipt_has_actual_withdrawal (event : Event (fromHistory bound) originInputs)
    (claim : Claim (fromHistory bound) originInputs) (origin : Financial.InstructionOrigin (I (fromHistory bound) originInputs))
    (receipt : Event.RemoteResolvedAt (fromHistory bound) originInputs event claim origin) :
    ∃ (actualInputs : List (RawEvent Party Good Port (State Party Technology) Instrument))
      (target : Target (fromHistory bound) claim actualInputs) (attempt : Attempt (fromHistory bound) actualInputs target.claim),
      event = .remoteAttempt claim actualInputs target attempt ∧
      (law base scope).Valid (attempt.position.item (fromHistory bound) actualInputs).before (attempt.position.item (fromHistory bound) actualInputs).request ∧
      ((law base scope).step (attempt.position.item (fromHistory bound) actualInputs).before (attempt.position.item (fromHistory bound) actualInputs).request).technology.holder = none ∧
      ((law base scope).step (attempt.position.item (fromHistory bound) actualInputs).before (attempt.position.item (fromHistory bound) actualInputs).request).technology.offered = none ∧
      ((law base scope).step (attempt.position.item (fromHistory bound) actualInputs).before (attempt.position.item (fromHistory bound) actualInputs).request).technology.version =
        (target.snapshot (Mandate.Challenge.fromHistory bound)).version + 1 := by
  cases event with
  | birth original => exact nomatch receipt
  | reaffirm original previous renewed => exact nomatch receipt
  | attempt original previous attempted => exact nomatch receipt
  | remoteReaffirm original actualInputs previous renewed => exact nomatch receipt
  | scopeBoundary original source laterWindow boundary => exact nomatch receipt
  | remoteAttempt original actualInputs target attempt =>
    rcases receipt with ⟨rfl, _, accepted⟩
    exact ⟨actualInputs, target, attempt, rfl, accepted, attempt.actual_withdrawal (Mandate.Challenge.fromHistory bound) actualInputs _ accepted⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross
