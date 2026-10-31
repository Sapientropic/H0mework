import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Native

/-! A later scope's real boundary extends any prior process on the original
Challenge vocabulary. Original snapshots stay literal; no cross-scope
receipt discharges an old withdrawal request. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.ScopeProcess

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)} {Index : Type}
  (bound : ProgrammeFamily base scope Index) (originInputs : Index)
  (source : ScopeBoundary.Source base) (laterWindow : scope.task.deadline < source.scope.task.earliest)
  (prior : NativeResponsibilityProcess (V bound originInputs)) (original : Claim bound originInputs)
noncomputable section

inductive Boundary (obligation : AdmittedObligation (V bound originInputs)) where
  | inherited (event : prior.BoundaryEvent obligation)
  | actual (receipt : ScopeBoundary.Receipt source)
      (content : obligation.content = original) (scope : obligation.scope = original.origin bound originInputs)
      (anchor : (obligation.admission.sourceEvent.claim bound originInputs).origin bound originInputs = original.origin bound originInputs)

def event (receipt : ScopeBoundary.Receipt source) : Event bound originInputs := .scopeBoundary original source laterWindow receipt

def carry (obligation : AdmittedObligation (V bound originInputs))
    (content : obligation.content = original) (jurisdiction : obligation.scope = original.origin bound originInputs)
    (receipt : ScopeBoundary.Receipt source) : ActiveCarryDisposition (V bound originInputs) obligation (event bound originInputs source laterWindow original receipt) := by
  if accepted : receipt.accepted source = true then
    exact .maintained ⟨content.symm,by rw [content]; exact jurisdiction,accepted⟩
  else
    exact .deferred (.inr ⟨content.symm,by rw [content]; exact jurisdiction,Bool.eq_false_of_not_eq_true accepted⟩)

def disposition (obligation : AdmittedObligation (V bound originInputs))
    (content : obligation.content = original) (jurisdiction : obligation.scope = original.origin bound originInputs)
    (receipt : ScopeBoundary.Receipt source) : BoundaryDisposition (V bound originInputs) obligation (event bound originInputs source laterWindow original receipt) :=
  .carry (carry bound originInputs source laterWindow original obligation content jurisdiction receipt)

theorem disposition_keeps_the_entire_original_obligation (obligation : AdmittedObligation (V bound originInputs))
    (content : obligation.content = original) (jurisdiction : obligation.scope = original.origin bound originInputs)
    (receipt : ScopeBoundary.Receipt source) :
    (disposition bound originInputs source laterWindow original obligation content jurisdiction receipt).targetSlot = .live obligation := by
  unfold disposition carry
  split <;> rfl

theorem new_scope_cannot_fulfil_the_old_request (receipt : ScopeBoundary.Receipt source)
    (claim : Claim bound originInputs) (origin : Financial.InstructionOrigin (I bound originInputs)) :
    (V bound originInputs).FulfilledAt (event bound originInputs source laterWindow original receipt) claim origin → False := by
  intro impossible
  cases impossible with
  | inl impossible => exact nomatch impossible
  | inr impossible => exact nomatch impossible

def process : NativeResponsibilityProcess (V bound originInputs) where
  AdmissionEvent := prior.AdmissionEvent
  admissionPayload := prior.admissionPayload
  BoundaryEvent := Boundary bound originInputs source prior original
  boundarySource := fun next => match next with
    | .inherited next => prior.boundarySource next
    | .actual receipt _ _ _ => event bound originInputs source laterWindow original receipt
  boundary_anchor_eq := fun next => by
    cases next with
    | inherited next => exact prior.boundary_anchor_eq next
    | actual receipt content jurisdiction anchor =>
      change MinimalRegistrableSourceAnchor.canonical (original.origin bound originInputs) (original.origin bound originInputs) =
        MinimalRegistrableSourceAnchor.canonical _ _
      rw [anchor]
  boundary_incidence_eq := fun next => by
    cases next with
    | inherited next => exact prior.boundary_incidence_eq next
    | actual receipt content jurisdiction anchor => exact anchor.symm
  boundaryDisposition := fun next => match next with
    | .inherited next => prior.boundaryDisposition next
    | .actual receipt content jurisdiction _ => disposition bound originInputs source laterWindow original _ content jurisdiction receipt
  ReopenEvent := prior.ReopenEvent
  reopenPayload := prior.reopenPayload

def inheritRun {first last : ResponsibilityState (V bound originInputs)} :
    prior.Run first last → (process bound originInputs source laterWindow prior original).Run first last
  | .nil => .nil
  | .step path (.admit next) => .step (inheritRun path) (.admit next)
  | .step path (.cross slot obligation present next) => .step (inheritRun path) (.cross slot obligation present (.inherited next))
  | .step path (.reopen slot archive present next) => .step (inheritRun path) (.reopen slot archive present next)

theorem inheritRun_events {first last : ResponsibilityState (V bound originInputs)} (path : prior.Run first last) :
    (inheritRun bound originInputs source laterWindow prior original path).events = path.events := by
  induction path with
  | nil => rfl
  | step path edge ih => cases edge <;> simp only [inheritRun,NativeResponsibilityProcess.Run.events,ih] <;> rfl

inductive Shape (state : ResponsibilityState (V bound originInputs)) where
  | pending (obligation : AdmittedObligation (V bound originInputs)) (slots : state.slots = [.live obligation])
      (content : obligation.content = original) (jurisdiction : obligation.scope = original.origin bound originInputs)
      (anchor : (obligation.admission.sourceEvent.claim bound originInputs).origin bound originInputs = original.origin bound originInputs)
  | closed (archive : TerminalArchive (V bound originInputs)) (slots : state.slots = [.terminal archive])

variable {prior original}
structure Thread (origin : prior.GeneratedState) where
  private mk ::
  state : (process bound originInputs source laterWindow prior original).GeneratedState
  slots : state.current.slots = origin.current.slots
  crossing : (process bound originInputs source laterWindow prior original).Run origin.current state.current

def begin (origin : prior.GeneratedState) : Thread bound originInputs source laterWindow (original := original) origin :=
  ⟨⟨origin.current,inheritRun bound originInputs source laterWindow prior original origin.generated⟩,rfl,.nil⟩

variable {origin : prior.GeneratedState}

def Thread.step (shape : Shape bound originInputs original origin.current)
    (thread : Thread bound originInputs source laterWindow (original := original) origin) (receipt : ScopeBoundary.Receipt source) :
    Thread bound originInputs source laterWindow (original := original) origin := by
  cases shape with
  | pending obligation slots content jurisdiction anchor =>
    have live := thread.slots.trans slots
    let address : Fin thread.state.current.slots.length := ⟨0,by rw [live]; exact Nat.zero_lt_succ 0⟩
    let edge : (process bound originInputs source laterWindow prior original).Edge thread.state.current :=
      .cross address obligation (by simp [address,live]) (.actual receipt content jurisdiction anchor)
    refine ⟨thread.state.step _ edge,?_,.step thread.crossing edge⟩
    change thread.state.current.slots.set address (disposition bound originInputs source laterWindow original obligation content jurisdiction receipt).targetSlot = _
    rw [disposition_keeps_the_entire_original_obligation]
    simp [address,live,slots]
  | closed archive slots => exact thread

def Thread.consume (shape : Shape bound originInputs original origin.current)
    (thread : Thread bound originInputs source laterWindow (original := original) origin) (receipts : List (ScopeBoundary.Receipt source)) :=
  receipts.foldl (Thread.step bound originInputs source laterWindow shape) thread

def image (obligation : AdmittedObligation (V bound originInputs))
    (content : obligation.content = original) (jurisdiction : obligation.scope = original.origin bound originInputs)
    (receipt : ScopeBoundary.Receipt source) : LifecycleEvent (V bound originInputs) :=
  .carried 0 obligation (event bound originInputs source laterWindow original receipt)
    (carry bound originInputs source laterWindow original obligation content jurisdiction receipt)

theorem Thread.step_history (obligation : AdmittedObligation (V bound originInputs))
    (slots : origin.current.slots = [.live obligation]) (content : obligation.content = original)
    (jurisdiction : obligation.scope = original.origin bound originInputs)
    (anchor : (obligation.admission.sourceEvent.claim bound originInputs).origin bound originInputs = original.origin bound originInputs)
    (thread : Thread bound originInputs source laterWindow (original := original) origin) (receipt : ScopeBoundary.Receipt source) :
    (thread.step bound originInputs source laterWindow (.pending obligation slots content jurisdiction anchor) receipt).state.current.history =
      thread.state.current.history ++ [image bound originInputs source laterWindow obligation content jurisdiction receipt] := rfl

theorem Thread.consume_history (obligation : AdmittedObligation (V bound originInputs))
    (slots : origin.current.slots = [.live obligation]) (content : obligation.content = original)
    (jurisdiction : obligation.scope = original.origin bound originInputs)
    (anchor : (obligation.admission.sourceEvent.claim bound originInputs).origin bound originInputs = original.origin bound originInputs)
    (thread : Thread bound originInputs source laterWindow (original := original) origin) (actual : List (ScopeBoundary.Receipt source)) :
    (thread.consume bound originInputs source laterWindow (.pending obligation slots content jurisdiction anchor) actual).state.current.history =
      thread.state.current.history ++ actual.map (image bound originInputs source laterWindow obligation content jurisdiction) := by
  induction actual generalizing thread with
  | nil => exact (List.append_nil _).symm
  | cons receipt rest ih =>
    change ((thread.step _ _ _ _ _ receipt).consume _ _ _ _ _ rest).state.current.history = _
    rw [ih,Thread.step_history]
    simp only [List.map_cons,List.append_assoc,List.singleton_append]

theorem Thread.closed_is_literal (archive : TerminalArchive (V bound originInputs))
    (slots : origin.current.slots = [.terminal archive])
    (thread : Thread bound originInputs source laterWindow (original := original) origin) (actual : List (ScopeBoundary.Receipt source)) :
    (thread.consume bound originInputs source laterWindow (.closed archive slots) actual).state = thread.state := by
  induction actual with
  | nil => rfl
  | cons receipt rest ih => exact ih

variable (prior original)
def edgeTrace {state : ResponsibilityState (V bound originInputs)} :
    (process bound originInputs source laterWindow prior original).Edge state → List (ScopeBoundary.Receipt source)
  | .cross _ _ _ (.actual receipt _ _ _) => [receipt]
  | _ => []
def actualTrace {first last : ResponsibilityState (V bound originInputs)} :
    (process bound originInputs source laterWindow prior original).Run first last → List (ScopeBoundary.Receipt source)
  | .nil => []
  | .step path edge => actualTrace path ++ edgeTrace bound originInputs source laterWindow prior original edge

theorem inheritRun_trace {first last : ResponsibilityState (V bound originInputs)} (path : prior.Run first last) :
    actualTrace bound originInputs source laterWindow prior original (inheritRun bound originInputs source laterWindow prior original path) = [] := by
  induction path with
  | nil => rfl
  | step path edge ih => cases edge <;> simp only [inheritRun,actualTrace,edgeTrace,List.append_nil,ih]

variable {prior original}
theorem Thread.consume_trace (obligation : AdmittedObligation (V bound originInputs))
    (slots : origin.current.slots = [.live obligation]) (content : obligation.content = original)
    (jurisdiction : obligation.scope = original.origin bound originInputs)
    (anchor : (obligation.admission.sourceEvent.claim bound originInputs).origin bound originInputs = original.origin bound originInputs)
    (thread : Thread bound originInputs source laterWindow (original := original) origin) (actual : List (ScopeBoundary.Receipt source)) :
    actualTrace bound originInputs source laterWindow prior original
      (thread.consume bound originInputs source laterWindow (.pending obligation slots content jurisdiction anchor) actual).state.generated =
      actualTrace bound originInputs source laterWindow prior original thread.state.generated ++ actual := by
  induction actual generalizing thread with
  | nil => exact (List.append_nil _).symm
  | cons receipt rest ih =>
    change actualTrace _ _ _ _ _ _ ((thread.step _ _ _ _ _ receipt).consume _ _ _ _ _ rest).state.generated = _
    rw [ih]
    change (_ ++ [receipt]) ++ rest = _ ++ (receipt :: rest)
    simp only [List.append_assoc,List.singleton_append]

theorem begin_trace (origin : prior.GeneratedState) (obligation : AdmittedObligation (V bound originInputs))
    (slots : origin.current.slots = [.live obligation]) (content : obligation.content = original)
    (jurisdiction : obligation.scope = original.origin bound originInputs)
    (anchor : (obligation.admission.sourceEvent.claim bound originInputs).origin bound originInputs = original.origin bound originInputs)
    (actual : List (ScopeBoundary.Receipt source)) :
    actualTrace bound originInputs source laterWindow prior original
      ((begin bound originInputs source laterWindow (original := original) origin).consume bound originInputs source laterWindow
        (.pending obligation slots content jurisdiction anchor) actual).state.generated = actual := by
  have consumed := Thread.consume_trace bound originInputs source laterWindow obligation slots content jurisdiction anchor
    (begin bound originInputs source laterWindow (original := original) origin) actual
  exact consumed.trans (congrArg (fun past => past ++ actual)
    (inheritRun_trace bound originInputs source laterWindow prior original origin.generated))

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.ScopeProcess
