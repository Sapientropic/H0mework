import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle

open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))
  (currentAt : Nat → RawCurrent Party Good (State Party Technology) Instrument)
  (wordAt : Nat → RawEvent Party Good Port (State Party Technology) Instrument)
  (birth : Nat) (grant : Grant base scope (currentAt birth) (wordAt birth))

abbrev vocabulary := Election.mandateVocabulary
  (Grant.lineageCompiler (Party := Party) (Port := Port))

def original : AdmittedObligation (vocabulary (Party := Party) (Port := Port)) :=
  Election.mandateObligation (Grant.lineageCompiler (Party := Party) (Port := Port)) grant.electionEvent

def Later (visit index : Nat) : Prop :=
  birth < visit ∨ (birth = visit ∧ grant.acceptance.item.val.index < index)

instance (visit index : Nat) : Decidable (Later base scope currentAt wordAt birth grant visit index) :=
  inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

def IsBoundary : Command Party → Prop
  | .renew | .exit | .revoke | .review => True
  | _ => False

instance (command : Command Party) : Decidable (IsBoundary command) := by
  cases command <;> dsimp [IsBoundary] <;> infer_instance

/-- This is an event of the original trace family, not a caller-selected
lifecycle verdict. A handoff carries both actual signatures of its successor. -/
inductive Event (obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))) where
  | private command
      (visit : Nat)
      (actual : ActualCommand base scope (currentAt visit) (wordAt visit))
      (later : Later base scope currentAt wordAt birth grant visit actual.item.val.index)
      (kind : IsBoundary actual.command)
      (origin : obligation = {original base scope currentAt wordAt birth grant with bearer := obligation.bearer})
  | private handoff
      (visit : Nat)
      (next : Grant base scope (currentAt visit) (wordAt visit))
      (later : Later base scope currentAt wordAt birth grant visit next.acceptance.item.val.index)
      (origin : obligation = {original base scope currentAt wordAt birth grant with bearer := obligation.bearer})

variable {base scope currentAt wordAt birth grant}

def Event.disposition
    {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Event base scope currentAt wordAt birth grant obligation) :
    BoundaryDisposition (vocabulary (Party := Party) (Port := Port)) obligation
      obligation.admission.sourceEvent := by
  exact
  match event with
  | .command _ actual _ _ _ =>
      if @Eq (Option Party) actual.after.technology.holder (some obligation.bearer) then
        .carry (.maintained .generated)
      else .bearerRelease (.jurisdictionEndedWithResidue .generated .generated)
  | .handoff _ next _ _ => .carry (.transferred next.candidate .generated)

def Event.next
    {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Event base scope currentAt wordAt birth grant obligation) :
    AdmittedObligation (vocabulary (Party := Party) (Port := Port)) :=
  match event with
  | .command .. => obligation
  | .handoff _ next _ _ => {obligation with bearer := next.candidate}

theorem Event.target_is_live
    {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Event base scope currentAt wordAt birth grant obligation) :
    event.disposition.targetSlot = .live event.next := by
  rcases event with ⟨visit, actual, later, kind, origin⟩ | ⟨visit, next, later, origin⟩
  · simp only [Event.disposition, Event.next]
    split <;> rfl
  · rfl

theorem Event.next_origin
    {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Event base scope currentAt wordAt birth grant obligation) :
    event.next = {original base scope currentAt wordAt birth grant with bearer := event.next.bearer} := by
  rcases event with ⟨visit, actual, later, kind, origin⟩ | ⟨visit, next, later, origin⟩
  · exact origin
  · dsimp [Event.next]
    rw [origin]

/-- Boundary-only continuation of the existing admission. No second admission,
vocabulary, obligation slot, or terminal constructor is available here. -/
def process : NativeResponsibilityProcess (vocabulary (Party := Party) (Port := Port)) where
  AdmissionEvent := Empty
  admissionPayload := fun event => nomatch event
  BoundaryEvent := Event base scope currentAt wordAt birth grant
  boundarySource := fun {obligation} _ => obligation.admission.sourceEvent
  boundary_anchor_eq := fun _ => rfl
  boundary_incidence_eq := fun _ => rfl
  boundaryDisposition := Event.disposition
  ReopenEvent := fun _ => Empty
  reopenPayload := fun event => nomatch event

def readEvent
    (obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port)))
    (origin : obligation = {original base scope currentAt wordAt birth grant with bearer := obligation.bearer})
    (visit : Nat) (actual : ActualCommand base scope (currentAt visit) (wordAt visit)) :
    Option (Event base scope currentAt wordAt birth grant obligation) :=
  if later : Later base scope currentAt wordAt birth grant visit actual.item.val.index then
    if boundary : IsBoundary actual.command then
      some (.command visit actual later boundary origin)
    else if actual.command = .accept then
      ((grantsAt base scope (currentAt visit) (wordAt visit)).filterMap fun next =>
        if position : next.acceptance.item.val.index = actual.item.val.index then
          some (Event.handoff visit next (position ▸ later) origin)
        else none).head?
    else none
  else none

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle
