import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Actual

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed

open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))
  (currentAt : Nat → RawCurrent Party Good (State Party Technology) Instrument)
  (wordAt : Nat → RawEvent Party Good Port (State Party Technology) Instrument)
  (birth : Nat) (grant : Grant base scope (currentAt birth) (wordAt birth))

def Authentic (current : RawCurrent Party Good (State Party Technology) Instrument)
    (attempt : Request Party Good Port (State Party Technology) Instrument)
    (operator : Party) (target : State Party Technology) (command : Command Party) : Prop :=
  operator = attempt.signer ∧ attempt.consents = [] ∧ attempt.purpose = scope.challenge ∧
    attempt.gates = [scope.challenge] ∧ target = advance scope current command ∧
    CanRun scope current attempt.signer command

instance (current : RawCurrent Party Good (State Party Technology) Instrument)
    (attempt : Request Party Good Port (State Party Technology) Instrument)
    (operator : Party) (target : State Party Technology) (command : Command Party) :
    Decidable (Authentic scope current attempt operator target command) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A refused boundary belongs to this raw execution, after the original
admission. It does not authorize its attempted command. -/
structure Refusal (obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))) where
  private mk ::
  visit : Nat
  item : {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)}
  operator : Party
  target : State Party Technology
  command : Command Party
  operation : item.val.request.operation = .revise operator target
  marked : target.last = some command
  authentic : Authentic scope item.val.before item.val.request operator target command
  refused : ¬ (law base scope).Valid item.val.before item.val.request
  later : Later base scope currentAt wordAt birth grant visit item.val.index
  kind : IsBoundary command
  origin : obligation = {original base scope currentAt wordAt birth grant with bearer := obligation.bearer}

inductive Event (obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))) where
  | private accepted (event : Lifecycle.Event base scope currentAt wordAt birth grant obligation)
  | private refused (evidence : Refusal base scope currentAt wordAt birth grant obligation)

variable {base scope currentAt wordAt birth grant}

/-- Release records an actually held jurisdiction ending; a review while
already unseated maintains the responsibility without inventing a release. -/
def acceptedDisposition
    {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Lifecycle.Event base scope currentAt wordAt birth grant obligation) :
    BoundaryDisposition (vocabulary (Party := Party) (Port := Port)) obligation obligation.admission.sourceEvent := by
  rcases event with ⟨visit, actual, later, kind, origin⟩ | ⟨visit, next, later, origin⟩
  · exact if @Eq (Option Party) actual.item.val.before.technology.holder (some obligation.bearer) ∧
        ¬ @Eq (Option Party) actual.after.technology.holder (some obligation.bearer) then
      .bearerRelease (.jurisdictionEndedWithResidue .generated .generated)
    else .carry (.maintained .generated)
  · exact .carry (.transferred next.candidate .generated)

def Event.disposition
    {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Event base scope currentAt wordAt birth grant obligation) :
    BoundaryDisposition (vocabulary (Party := Party) (Port := Port)) obligation obligation.admission.sourceEvent :=
  match event with
  | .accepted event => acceptedDisposition event
  | .refused _ => .carry (.deferred .generated)

def Event.next
    {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Event base scope currentAt wordAt birth grant obligation) :
    AdmittedObligation (vocabulary (Party := Party) (Port := Port)) :=
  match event with
  | .accepted event => event.next
  | .refused _ => obligation

theorem Event.target_is_live
    {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Event base scope currentAt wordAt birth grant obligation) :
    event.disposition.targetSlot = .live event.next := by
  rcases event with ⟨event⟩ | ⟨evidence⟩
  · rcases event with ⟨visit, actual, later, kind, origin⟩ | ⟨visit, next, later, origin⟩
    · dsimp [Event.disposition, acceptedDisposition, Event.next, Lifecycle.Event.next]
      split <;> rfl
    · rfl
  · rfl

theorem Event.next_origin
    {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Event base scope currentAt wordAt birth grant obligation) :
    event.next = {original base scope currentAt wordAt birth grant with bearer := event.next.bearer} := by
  rcases event with ⟨event⟩ | ⟨evidence⟩
  · exact event.next_origin
  · exact evidence.origin

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
    (visit : Nat)
    (item : {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)}) :
    Option (Event base scope currentAt wordAt birth grant obligation) :=
  match recognize base scope _ _ item with
  | some actual => (Lifecycle.readEvent obligation origin visit actual).map Event.accepted
  | none =>
      match operation : item.val.request.operation with
      | .revise operator target =>
          match marked : target.last with
          | some command =>
              if refused : ¬ (law base scope).Valid item.val.before item.val.request then
                if later : Later base scope currentAt wordAt birth grant visit item.val.index then
                  if kind : IsBoundary command then
                    if authentic : Authentic scope item.val.before item.val.request operator target command then
                      some (.refused ⟨visit, item, operator, target, command, operation, marked,
                        authentic, refused, later, kind, origin⟩)
                    else none
                  else none
                else none
              else none
          | none => none
      | _ => none

theorem refused_event_is_guarded_native_defer
    {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (evidence : Refusal base scope currentAt wordAt birth grant obligation) :
    (Event.refused evidence).disposition = .carry (.deferred .generated) ∧
    (Event.refused evidence).next = obligation ∧
    evidence.item.val ∈ (law base scope).rawItems (currentAt evidence.visit) (wordAt evidence.visit) ∧
    ¬ (law base scope).Valid evidence.item.val.before evidence.item.val.request :=
  ⟨rfl, rfl, evidence.item.property, evidence.refused⟩


theorem every_authentic_refusal_generates_a_native_defer
    {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (evidence : Refusal base scope currentAt wordAt birth grant obligation) :
    ∃ event : Event base scope currentAt wordAt birth grant obligation,
      readEvent obligation evidence.origin evidence.visit evidence.item = some event ∧
      event.disposition = .carry (.deferred .generated) ∧ event.next = obligation := by
  refine ⟨Event.refused evidence, ?_, rfl, rfl⟩
  rcases evidence with ⟨visit, ⟨⟨index, before, attempt⟩, member⟩, operator, target, command,
    operation, marked, authentic, refused, later, kind, origin⟩
  cases attempt with
  | mk signer consents purpose gates rawOperation =>
      dsimp at operation
      subst rawOperation
      cases target with
      | mk technology version holder offered last =>
          dsimp at marked
          subst last
          simp only [readEvent, recognize, dif_neg refused, dif_pos refused,
            dif_pos later, dif_pos kind, dif_pos authentic]

variable (base scope currentAt wordAt birth grant)

abbrev initialState := (admitGrant base scope _ _ grant).native.target

/-- The full dependent Run retains each actual command or two-signature
handoff. Its history alone is deliberately not the installed payload. -/
structure History where
  private mk ::
  obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))
  origin : obligation = {original base scope currentAt wordAt birth grant with bearer := obligation.bearer}
  state : ResponsibilityState (vocabulary (Party := Party) (Port := Port))
  slots : state.slots = [.live obligation]
  generated : (process (base := base) (scope := scope) (currentAt := currentAt)
    (wordAt := wordAt) (birth := birth) (grant := grant)).Run
    (initialState base scope currentAt wordAt birth grant) state

variable {base scope currentAt wordAt birth grant}

def initial : History base scope currentAt wordAt birth grant :=
  ⟨original base scope currentAt wordAt birth grant, rfl,
    initialState base scope currentAt wordAt birth grant, rfl, .nil⟩

def History.slot (history : History base scope currentAt wordAt birth grant) :
    Fin history.state.slots.length :=
  ⟨0, by rw [history.slots]; exact Nat.zero_lt_succ 0⟩

theorem History.present (history : History base scope currentAt wordAt birth grant) :
    history.state.slots.get history.slot = .live history.obligation := by
  simp [History.slot, history.slots]

def History.edge (history : History base scope currentAt wordAt birth grant)
    (event : Event base scope currentAt wordAt birth grant history.obligation) :=
  NativeResponsibilityProcess.Edge.cross
    (P := process (base := base) (scope := scope) (currentAt := currentAt)
      (wordAt := wordAt) (birth := birth) (grant := grant))
    history.slot history.obligation history.present event

def History.cross (history : History base scope currentAt wordAt birth grant)
    (event : Event base scope currentAt wordAt birth grant history.obligation) :
    History base scope currentAt wordAt birth grant where
  obligation := event.next
  origin := event.next_origin
  state := (history.edge event).target
  slots := by
    change history.state.slots.set history.slot event.disposition.targetSlot = _
    rw [event.target_is_live]
    simp [History.slot, history.slots]
  generated := .step history.generated (history.edge event)

def History.consume (history : History base scope currentAt wordAt birth grant)
    (visit : Nat)
    (item : {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)}) :
    History base scope currentAt wordAt birth grant :=
  match readEvent history.obligation history.origin visit item with
  | none => history
  | some event => history.cross event

def History.visit (history : History base scope currentAt wordAt birth grant) (visit : Nat) :
    History base scope currentAt wordAt birth grant :=
  ((law base scope).rawItems (currentAt visit) (wordAt visit)).attach.foldl
    (fun prior item => prior.consume visit item) history

theorem History.authentic_refusal_is_an_actual_native_crossing
    (history : History base scope currentAt wordAt birth grant)
    (evidence : Refusal base scope currentAt wordAt birth grant history.obligation) :
    ∃ event : Event base scope currentAt wordAt birth grant history.obligation,
      history.consume evidence.visit evidence.item = history.cross event ∧
      event.disposition = .carry (.deferred .generated) ∧ event.next = history.obligation := by
  obtain ⟨event, read, deferred, next⟩ := every_authentic_refusal_generates_a_native_defer evidence
  refine ⟨event, ?_, deferred, next⟩
  unfold History.consume
  rw [show history.origin = evidence.origin from Subsingleton.elim _ _, read]

/-- Only the observed finite prefix is consumed, in source order. Later
visits are not evaluated or stored as a successful future. -/
def through (last : Nat) : History base scope currentAt wordAt birth grant :=
  (List.range (last + 1)).foldl (fun history visit => history.visit visit) initial

theorem through_succ (last : Nat) :
    (through (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt)
      (birth := birth) (grant := grant) last).visit (last + 1) = through (last + 1) := by
  simp only [through, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem History.original_admission (history : History base scope currentAt wordAt birth grant) :
    HEq history.obligation.admission (original base scope currentAt wordAt birth grant).admission := by
  rw [history.origin]

theorem History.original_scope_lineage_incidence (history : History base scope currentAt wordAt birth grant) :
    history.obligation.scope = scope.service ∧
    history.obligation.lineage = (original base scope currentAt wordAt birth grant).lineage ∧
    history.obligation.sourceIncidence = (original base scope currentAt wordAt birth grant).sourceIncidence := by
  rw [history.origin]
  exact ⟨rfl, rfl, rfl⟩

theorem History.responsibility_remains_live (history : History base scope currentAt wordAt birth grant) :
    history.state.LiveAt 0 := by
  refine ⟨history.obligation, ?_⟩
  rw [history.slots]
  rfl

theorem through_keeps_original_responsibility (last : Nat) :
    (through (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt)
      (birth := birth) (grant := grant) last).state.LiveAt 0 :=
  History.responsibility_remains_live _


end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed
