import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Native

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
  (limit : Nat)
  (common : ∀ ordinal < limit,
    Registered.traceItems (I bound nextInputs) (ProgrammeHistory.visitAt (I bound nextInputs) ordinal).current =
      Registered.traceItems (I bound inputs) (ProgrammeHistory.visitAt (I bound inputs) ordinal).current)

def position (original : Position bound inputs) (inside : original.ordinal < limit) :
    Position bound nextInputs :=
  ⟨original.ordinal, ⟨original.index.val, by rw [common original.ordinal inside]; exact original.index.isLt⟩⟩

theorem position_same_item (original : Position bound inputs) (inside : original.ordinal < limit) :
    (position bound limit common original inside).item bound nextInputs = original.item bound inputs := by
  have same := congrArg (fun items => items[original.index.val]?) (common original.ordinal inside)
  have newBound : original.index.val < (Registered.traceItems (I bound nextInputs)
      (ProgrammeHistory.visitAt (I bound nextInputs) original.ordinal).current).length :=
    (position bound limit common original inside).index.isLt
  rw [List.getElem?_eq_getElem newBound,
    List.getElem?_eq_getElem original.index.isLt] at same
  exact Option.some.inj same

def replacement (original : Claim bound inputs) (inside : original.position.ordinal < limit) :
    Claim bound nextInputs :=
  let target := position bound limit common original.position inside
  have found : (read bound nextInputs target).isSome = true := by
    unfold read
    have same := position_same_item bound limit common original.position inside
    have signed : Submission (scope := scope) (target.item bound _).request := by rw [same]; exact original.signed
    have accepted : (law base scope).Valid (target.item bound _).before (target.item bound _).request := by rw [same]; exact original.accepted
    have active : (target.item bound _).before.technology.holder.isSome = true ∨
        (target.item bound _).before.technology.offered.isSome = true := by rw [same]; exact original.active
    rw [dif_pos signed, dif_pos accepted, dif_pos active]
    rfl
  (read bound nextInputs target).get found

theorem replacement_position (original : Claim bound inputs) (inside : original.position.ordinal < limit) :
    (replacement bound limit common original inside).position = position bound limit common original.position inside :=
  read_position _ _ _ _ (Option.some_get _).symm

theorem replacement_same_item_and_snapshot (original : Claim bound inputs) (inside : original.position.ordinal < limit) :
    (replacement bound limit common original inside).position.item bound nextInputs = original.position.item bound inputs ∧
    (replacement bound limit common original inside).snapshot bound nextInputs = original.snapshot bound inputs ∧
    (replacement bound limit common original inside).signer bound nextInputs = original.signer bound inputs ∧
    (replacement bound limit common original inside).position.ordinal = original.position.ordinal ∧
    (replacement bound limit common original inside).position.index.val = original.position.index.val := by
  unfold Claim.snapshot Claim.signer
  rw [show (replacement bound limit common original inside).position = _ from replacement_position bound limit common original inside]
  have same := position_same_item bound limit common original.position inside
  exact ⟨same, congrArg (fun item => item.before.technology) same, congrArg (fun item => item.request.signer) same, rfl, rfl⟩

def Within (count : Nat) : History bound original inputs → Prop
  | .pending target _ _ => target.claim.position.ordinal < count
  | .closed .. => True

def transportAnchor (anchor : Anchor bound original inputs)
    (inside : anchor.image.position.ordinal < limit) : Anchor bound original nextInputs where
  image := replacement bound limit common anchor.image inside
  ordinal := (replacement_same_item_and_snapshot bound limit common anchor.image inside).2.2.2.1.trans anchor.ordinal
  index := (replacement_same_item_and_snapshot bound limit common anchor.image inside).2.2.2.2.trans anchor.index
  item := (replacement_same_item_and_snapshot bound limit common anchor.image inside).1.trans anchor.item
  common := fun ordinal before => (common ordinal (by rw [anchor.ordinal] at inside; omega)).trans
    (anchor.common ordinal before)

def transportTarget (target : Target bound original inputs)
    (inside : target.claim.position.ordinal < limit) : Target bound original nextInputs where
  anchor := transportAnchor bound limit common target.anchor (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)
  claim := replacement bound limit common target.claim inside
  afterOrigin := by
    change (replacement bound limit common target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).position.ordinal <
        (replacement bound limit common target.claim inside).position.ordinal ∨
      ((replacement bound limit common target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).position.ordinal =
          (replacement bound limit common target.claim inside).position.ordinal ∧
        (replacement bound limit common target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).position.index.val ≤
          (replacement bound limit common target.claim inside).position.index.val)
    have originOrdinal := (replacement_same_item_and_snapshot bound limit common target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).2.2.2.1
    have targetOrdinal := (replacement_same_item_and_snapshot bound limit common target.claim inside).2.2.2.1
    have originIndex := (replacement_same_item_and_snapshot bound limit common target.anchor.image (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).2.2.2
    have targetIndex := (replacement_same_item_and_snapshot bound limit common target.claim inside).2.2.2.2
    rcases target.afterOrigin with later | ⟨same, index⟩ <;> omega

  signer := (replacement_same_item_and_snapshot bound limit common target.claim inside).2.2.1.trans
    (target.signer.trans (replacement_same_item_and_snapshot bound limit common target.anchor.image
      (Nat.lt_of_le_of_lt target.origin_ordinal_le inside)).2.2.1.symm)

theorem transported_target_keeps_snapshot (target : Target bound original inputs)
    (inside : target.claim.position.ordinal < limit) : (transportTarget bound limit common target inside).snapshot bound = target.snapshot bound :=
  (replacement_same_item_and_snapshot bound limit common target.claim inside).2.1

def transportHistory (history : History bound original inputs)
    (within : Within bound (limit) history) : History bound original nextInputs := by
  cases history with
  | closed state archive slots => exact .closed state archive slots
  | pending target state slots =>
      let next := transportTarget bound limit common target within
      have same : tracked bound next = tracked bound target :=
        congrArg (fun residual : State Party Technology => { obligation bound originInputs original with residual := residual })
          (transported_target_keeps_snapshot bound limit common target within)
      exact .pending next state (slots.trans (congrArg (fun obligation => [ObligationSlot.live obligation]) same).symm)

theorem transport_preserves_the_entire_generated_state
    (history : History bound original inputs) (within : Within bound (limit) history) :
    (transportHistory bound limit common history within).state = history.state := by cases history <;> rfl

theorem transport_preserves_archived_receipt
    (state : (process bound original).GeneratedState) (archive : TerminalArchive (V bound originInputs))
    (slots : state.current.slots = [.terminal archive]) :
    transportHistory bound (inputs := inputs) limit common (.closed state archive slots) True.intro = .closed state archive slots := rfl

def receiveRun (history : History bound original inputs) (position : Position bound inputs) :
    (process bound original).Run history.state.current (history.receive bound position).state.current := by
  cases history with
  | closed state archive slots => exact .nil
  | pending target state slots =>
    cases renewed : readReconfirmation bound target position with
    | some receipt =>
      simp only [History.receive, renewed]
      exact .step .nil (.cross (P := process bound original) ⟨0, by simp [History.state, slots]⟩
        (tracked bound target) (by simp [History.state, slots]) (.reaffirm target receipt rfl))
    | none =>
      cases attempted : readAttempt bound inputs target.claim position with
      | none => simp only [History.receive, renewed, attempted]; exact .nil
      | some receipt =>
        simp only [History.receive, renewed, attempted]
        split
        · exact .step .nil (.cross (P := process bound original) ⟨0, by simp [History.state, slots]⟩
            (tracked bound target) (by simp [History.state, slots]) (.attempt target receipt rfl))
        · exact .step .nil (.cross (P := process bound original) ⟨0, by simp [History.state, slots]⟩
            (tracked bound target) (by simp [History.state, slots]) (.attempt target receipt rfl))

def visitRun (history : History bound original inputs) (positions : List (Position bound inputs)) :
    (process bound original).Run history.state.current (positions.foldl (History.receive bound) history).state.current := by
  induction positions generalizing history with
  | nil => exact .nil
  | cons position tail ih => exact (receiveRun bound history position).concatRuns _ (ih (history.receive bound position))


end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Programme
