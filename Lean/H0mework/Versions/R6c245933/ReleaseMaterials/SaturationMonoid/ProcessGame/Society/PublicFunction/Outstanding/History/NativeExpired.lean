import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeThread

/-! Actual later-source visits maintain expired original services in their
original vocabulary. Every old edge is inherited; a terminal state stays
literal, while each live slot receives an actual maintenance boundary. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService.Expired

open ResponsibilityLifecycle Institutions.Capitalism.Universal.Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (originInputs : List (RawEvent Party Good Port Technology Instrument))
noncomputable section

abbrev prior := threadProcess source originInputs

inductive Boundary (obligation : AdmittedObligation (V source originInputs)) where
  | inherited (event : (prior source originInputs).BoundaryEvent obligation)
  | observed (index : source.Slot) (input : ExpiredInput source)
      (content : obligation.content = index) (scope : obligation.scope = index)
      (admission : obligation.admission.sourceEvent.index = index)

def process : NativeResponsibilityProcess (V source originInputs) where
  AdmissionEvent := (prior source originInputs).AdmissionEvent
  admissionPayload := (prior source originInputs).admissionPayload
  BoundaryEvent := Boundary source originInputs
  boundarySource := fun event => match event with
    | .inherited event => (prior source originInputs).boundarySource event
    | .observed index input _ _ _ => expiredEvent source originInputs index input
  boundary_anchor_eq := fun {obligation} event => by
    cases event with
    | inherited event => exact (prior source originInputs).boundary_anchor_eq event
    | observed index input content scope admission =>
      change MinimalRegistrableSourceAnchor.canonical index index =
        MinimalRegistrableSourceAnchor.canonical obligation.admission.sourceEvent.index obligation.admission.sourceEvent.index
      rw [admission]
  boundary_incidence_eq := fun event => by
    cases event with
    | inherited event => exact (prior source originInputs).boundary_incidence_eq event
    | observed index input content scope admission => exact admission.symm
  boundaryDisposition := fun event => match event with
    | .inherited event => (prior source originInputs).boundaryDisposition event
    | .observed index input content scope _ => .carry (.maintained
        ⟨content,scope,expiredReceipt source originInputs index input,
          expired_event_cannot_fulfil_the_original_window source originInputs index input⟩)
  ReopenEvent := (prior source originInputs).ReopenEvent
  reopenPayload := (prior source originInputs).reopenPayload

def inheritRun {first last : ResponsibilityState (V source originInputs)} :
    (prior source originInputs).Run first last → (process source originInputs).Run first last
  | .nil => .nil
  | .step path (.admit event) => .step (inheritRun path) (.admit event)
  | .step path (.cross slot obligation present event) =>
      .step (inheritRun path) (.cross slot obligation present (.inherited event))
  | .step path (.reopen slot archive present event) => .step (inheritRun path) (.reopen slot archive present event)

theorem inheritRun_events {first last : ResponsibilityState (V source originInputs)}
    (path : (prior source originInputs).Run first last) :
    (inheritRun source originInputs path).events = path.events := by
  induction path with
  | nil => rfl
  | step path edge ih => cases edge <;> simp only [inheritRun, NativeResponsibilityProcess.Run.events, ih] <;> rfl

def edgeTrace {state : ResponsibilityState (V source originInputs)} :
    (process source originInputs).Edge state → List (ExpiredInput source)
  | .cross _ _ _ (.observed _ input _ _ _) => [input]
  | _ => []

def actualTrace {first last : ResponsibilityState (V source originInputs)} :
    (process source originInputs).Run first last → List (ExpiredInput source)
  | .nil => []
  | .step path edge => actualTrace path ++ edgeTrace source originInputs edge

theorem inheritRun_trace {first last : ResponsibilityState (V source originInputs)}
    (path : (prior source originInputs).Run first last) : actualTrace source originInputs (inheritRun source originInputs path) = [] := by
  induction path with
  | nil => rfl
  | step path edge ih => cases edge <;> simp only [inheritRun,actualTrace,edgeTrace,List.append_nil,ih]

variable {originInputs} {inputs : List (RawEvent Party Good Port Technology Instrument)} {index : source.Slot}

structure Continuation (original : Thread source originInputs index inputs) where
  private mk ::
  state : (process source originInputs).GeneratedState
  slots : state.current.slots = original.state.current.slots
  crossing : (process source originInputs).Run original.state.current state.current

def begin (original : Thread source originInputs index inputs) : Continuation source original :=
  ⟨⟨original.state.current,inheritRun source originInputs original.state.generated⟩,rfl,.nil⟩

def Continuation.step {original : Thread source originInputs index inputs}
    (thread : Continuation source original) (input : ExpiredInput source) : Continuation source original := by
  cases original.shape with
  | live unpaid slots =>
    have live : thread.state.current.slots = [.live (obligation source originInputs index)] := thread.slots.trans slots
    let address : Fin thread.state.current.slots.length := ⟨0,by rw [live]; exact Nat.zero_lt_succ 0⟩
    let edge : (process source originInputs).Edge thread.state.current :=
      .cross address (obligation source originInputs index) (by simp [address,live]) (.observed index input rfl rfl rfl)
    refine ⟨thread.state.step (process source originInputs) edge,?_,.step thread.crossing edge⟩
    change thread.state.current.slots.set address (.live (obligation source originInputs index)) = _
    simp [address,live,slots]
  | terminal archive paid recorded original slots => exact thread

def Continuation.consume {original : Thread source originInputs index inputs}
    (thread : Continuation source original) (observations : List (ExpiredInput source)) : Continuation source original :=
  observations.foldl (Continuation.step source) thread

def image (originInputs : List (RawEvent Party Good Port Technology Instrument))
    (index : source.Slot) (input : ExpiredInput source) : LifecycleEvent (V source originInputs) :=
  .carried 0 (obligation source originInputs index) (expiredEvent source originInputs index input)
    (.maintained ⟨rfl,rfl,expiredReceipt source originInputs index input,
      expired_event_cannot_fulfil_the_original_window source originInputs index input⟩)

theorem Continuation.step_history {original : Thread source originInputs index inputs}
    (thread : Continuation source original)
    (live : original.state.current.slots = [.live (obligation source originInputs index)]) (input : ExpiredInput source) :
    (thread.step source input).state.current.history = thread.state.current.history ++ [image source originInputs index input] := by
  rcases original with ⟨originalState,originalShape⟩
  cases originalShape with
  | live unpaid slots => rfl
  | terminal archive paid recorded original_eq slots => rw [slots] at live; cases live

theorem Continuation.consume_history {original : Thread source originInputs index inputs}
    (thread : Continuation source original)
    (live : original.state.current.slots = [.live (obligation source originInputs index)]) (observations : List (ExpiredInput source)) :
    (thread.consume source observations).state.current.history =
      thread.state.current.history ++ observations.map (image source originInputs index) := by
  induction observations generalizing thread with
  | nil => exact (List.append_nil _).symm
  | cons input rest ih =>
    change ((thread.step source input).consume source rest).state.current.history = _
    rw [ih,Continuation.step_history source thread live]
    simp only [List.map_cons,List.append_assoc,List.singleton_append]

theorem Continuation.terminal_state_is_literal {original : Thread source originInputs index inputs}
    (thread : Continuation source original) (terminal : original.state.current.TerminalAt 0)
    (observations : List (ExpiredInput source)) : (thread.consume source observations).state = thread.state := by
  have step_eq (thread : Continuation source original) (input : ExpiredInput source) : thread.step source input = thread := by
    rcases original with ⟨originalState,originalShape⟩
    cases originalShape with
    | live unpaid slots =>
      obtain ⟨archive,present⟩ := terminal
      simp only [slots,List.getElem?_cons_zero] at present
      cases present
    | terminal archive paid recorded original_eq slots => rfl
  induction observations generalizing thread with
  | nil => rfl
  | cons input rest ih =>
    change ((thread.step source input).consume source rest).state = _
    rw [step_eq]
    exact ih thread

theorem whole_original_history_precedes_actual_maintenance
    (original : Thread source originInputs index inputs)
    (live : original.state.current.slots = [.live (obligation source originInputs index)]) (observations : List (ExpiredInput source)) :
    ((begin source original).consume source observations).state.generated.events =
      original.state.generated.events ++ observations.map (image source originInputs index) := by
  rw [← NativeResponsibilityProcess.GeneratedState.history_eq]
  rw [Continuation.consume_history source _ live]
  change original.state.current.history ++ _ = _
  rw [original.state.history_eq]

theorem Continuation.consume_trace {original : Thread source originInputs index inputs}
    (thread : Continuation source original)
    (live : original.state.current.slots = [.live (obligation source originInputs index)]) (observations : List (ExpiredInput source)) :
    actualTrace source originInputs (thread.consume source observations).state.generated =
      actualTrace source originInputs thread.state.generated ++ observations := by
  have step_trace (thread : Continuation source original) (input : ExpiredInput source) :
      actualTrace source originInputs (thread.step source input).state.generated =
        actualTrace source originInputs thread.state.generated ++ [input] := by
    rcases original with ⟨originalState,originalShape⟩
    cases originalShape with
    | live unpaid slots => rfl
    | terminal archive paid recorded original_eq slots => rw [slots] at live; cases live
  induction observations generalizing thread with
  | nil => exact (List.append_nil _).symm
  | cons input rest ih =>
    change actualTrace source originInputs ((thread.step source input).consume source rest).state.generated = _
    rw [ih,step_trace]
    simp only [List.append_assoc,List.singleton_append]

theorem complete_actual_trace_is_the_original_observation_list
    (original : Thread source originInputs index inputs)
    (live : original.state.current.slots = [.live (obligation source originInputs index)]) (observations : List (ExpiredInput source)) :
    actualTrace source originInputs ((begin source original).consume source observations).state.generated = observations := by
  rw [Continuation.consume_trace source _ live]
  change actualTrace source originInputs (inheritRun source originInputs original.state.generated) ++ observations = _
  rw [inheritRun_trace,List.nil_append]

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService.Expired
