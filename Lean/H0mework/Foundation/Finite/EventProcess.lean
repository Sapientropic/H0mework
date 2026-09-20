import H0mework.Foundation.Authority.Receipt
import H0mework.Realization.Residual.NativeResponsibility

/-!
# Source-owned finite event-indexed residual dynamics

This is the branching counterpart of the existing deterministic constructive
residual process.  A source supplies only its dependent event family, update,
residual transport, emitted trace and recollection law.  Exact paths, ordered
traces, whole-path write-back and the native responsibility receipts are then
generated canonically.

The target of a step is never a field of a caller-facing receipt.  Distinct
events at one state may have distinct targets.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFiniteEventIndexedResidualProcess

universe u

/-- Source-owned branching residual dynamics. -/
structure Process : Type (u + 1) where
  State : Type u
  Residual : Type u
  Trace : Type u
  EventAt : State → Type u
  update : {state : State} → EventAt state → State
  update_ne : {state : State} → (event : EventAt state) → update event ≠ state
  residual : State → Residual
  keep : {state : State} → EventAt state → Residual → Residual
  residual_transport : {state : State} → (event : EventAt state) →
    residual (update event) = keep event (residual state)
  stepTrace : {state : State} → EventAt state → Trace
  recollect : Residual → Trace → Residual
  recollect_step : {state : State} → (event : EventAt state) →
    recollect (residual (update event)) (stepTrace event) = residual state

/-- Chronological path generated only by dependent source events. -/
inductive GeneratedPathAt (P : Process.{u})
    (source : P.State) : P.State → Type u
  | nil : GeneratedPathAt P source source
  | snoc {state : P.State}
      (prior : GeneratedPathAt P source state)
      (event : P.EventAt state) :
      GeneratedPathAt P source (P.update event)

namespace GeneratedPathAt

variable {P : Process.{u}} {source target : P.State}

def length : {target : P.State} → GeneratedPathAt P source target → Nat
  | _, .nil => 0
  | _, .snoc prior _ => prior.length + 1

def events : {target : P.State} → GeneratedPathAt P source target →
    List (Sigma P.EventAt)
  | _, .nil => []
  | _, .snoc prior event => prior.events ++ [⟨_, event⟩]

def trace : {target : P.State} → GeneratedPathAt P source target →
    List P.Trace
  | _, .nil => []
  | _, .snoc prior event => prior.trace ++ [P.stepTrace event]

def oneStep (state : P.State) (event : P.EventAt state) :
    GeneratedPathAt P state (P.update event) :=
  .snoc .nil event

end GeneratedPathAt

def Process.recollectTrace
    (P : Process.{u}) (live : P.Residual) : List P.Trace → P.Residual
  | [] => live
  | trace :: rest => P.recollect (P.recollectTrace live rest) trace

theorem Process.recollectTrace_append
    (P : Process.{u}) (live : P.Residual)
    (front suffix : List P.Trace) :
    P.recollectTrace live (front ++ suffix) =
      P.recollectTrace (P.recollectTrace live suffix) front := by
  induction front with
  | nil => rfl
  | cons trace tail inductionHypothesis =>
      simp only [List.cons_append, Process.recollectTrace]
      rw [inductionHypothesis]

theorem GeneratedPathAt.recollects_source
    {P : Process.{u}} {source target : P.State}
    (path : GeneratedPathAt P source target) :
    P.recollectTrace (P.residual target) path.trace =
      P.residual source := by
  induction path with
  | nil => rfl
  | snoc prior event inductionHypothesis =>
      rw [GeneratedPathAt.trace, P.recollectTrace_append]
      change
        P.recollectTrace
            (P.recollect (P.residual (P.update event))
              (P.stepTrace event))
            prior.trace =
          P.residual source
      rw [P.recollect_step]
      exact inductionHypothesis

/-- Whole-path write-back generated from one exact event path. -/
structure PathWriteBack
    (P : Process.{u}) {source target : P.State}
    (path : GeneratedPathAt P source target) : Type u where
  private mk ::
  live : P.Residual
  trace : List P.Trace
  live_eq : live = P.residual target
  trace_eq : trace = path.trace
  recollects_source : P.recollectTrace live trace = P.residual source

def GeneratedPathAt.writeBack
    {P : Process.{u}} {source target : P.State}
    (path : GeneratedPathAt P source target) : PathWriteBack P path :=
  ⟨P.residual target, path.trace, rfl, rfl, path.recollects_source⟩

/-- One exact emitted event with its source state. -/
structure SourceEvent (P : Process.{u}) : Type u where
  state : P.State
  event : P.EventAt state

namespace SourceEvent

variable {P : Process.{u}}

def target (source : SourceEvent P) : P.State :=
  P.update source.event

def path (source : SourceEvent P) :
    GeneratedPathAt P source.state source.target :=
  .oneStep source.state source.event

def trace (source : SourceEvent P) : P.Trace :=
  P.stepTrace source.event

def writeBack (source : SourceEvent P) : PathWriteBack P source.path :=
  source.path.writeBack

theorem target_ne_source (source : SourceEvent P) :
    source.target ≠ source.state :=
  P.update_ne source.event

end SourceEvent

/-- Canonical compiler output.  Target, path, trace and write-back are all
definitions of the same source event. -/
structure GeneratedStepAt (P : Process.{u}) : Type u where
  private mk ::
  source : SourceEvent P
  target : P.State
  target_eq : target = source.target
  path : GeneratedPathAt P source.state target
  path_eq : HEq path source.path
  trace : P.Trace
  trace_eq : trace = source.trace
  writeBack : PathWriteBack P path
  source_ne_target : source.state ≠ target

def canonicalCompile (P : Process.{u})
    (source : SourceEvent P) : GeneratedStepAt P :=
  ⟨source, source.target, rfl, source.path, HEq.rfl,
    source.trace, rfl, source.writeBack,
    Ne.symm source.target_ne_source⟩

def canonicalCompiler (P : Process.{u}) :
    CanonicalReceiptAuthority.Compiler (SourceEvent P) (GeneratedStepAt P) :=
  ⟨canonicalCompile P⟩

def canonicalCompile_isCanonical (P : Process.{u})
    (source : SourceEvent P) :
    CanonicalReceiptAuthority.CanonicalReceipt
      (canonicalCompiler P) (canonicalCompile P source) :=
  (canonicalCompiler P).compileCanonical source

/-- Public responsibility metadata for the already source-owned dynamics.
It cannot replace any update, target, trace, path or write-back. -/
structure Authority (P : Process.{u}) : Type (u + 1) where
  Content : Type u
  Bearer : Type u
  Scope : Type u
  Lineage : Type u
  Incidence : Type u
  SourceObservation : ComplementObservation.ComplementObservationCarrier.{u}
  content : P.State → Content
  anchor : {state : P.State} → P.EventAt state →
    MinimalRegistrableSourceAnchor SourceObservation Scope Lineage
  incidence : {state : P.State} → P.EventAt state → Incidence
  ObstructionAt : P.State → Type u
  obstructionContent : {state : P.State} → ObstructionAt state → Content
  obstructionState : {state : P.State} → ObstructionAt state → P.State
  admissionBearer : P.State → Bearer
  nextBearer : {state : P.State} → P.EventAt state → Bearer
  RouteAt : {state : P.State} →
    P.EventAt state → Bearer → Bearer → Type u
  routeReceipt : {state : P.State} → (event : P.EventAt state) →
    (oldBearer : Bearer) → RouteAt event oldBearer (nextBearer event)
  content_update : {state : P.State} → (event : P.EventAt state) →
    content (P.update event) = content state

structure KeepReceipt
    (P : Process.{u}) {state : P.State} (event : P.EventAt state) : Type u where
  residual_transport :
    P.residual (P.update event) = P.keep event (P.residual state)

def keepReceipt
    (P : Process.{u}) {state : P.State} (event : P.EventAt state) :
    KeepReceipt P event :=
  ⟨P.residual_transport event⟩

structure TraceReceipt
    (P : Process.{u}) {state : P.State} (event : P.EventAt state) : Type u where
  value : P.Trace
  value_eq : value = P.stepTrace event

def traceReceipt
    (P : Process.{u}) {state : P.State} (event : P.EventAt state) :
    TraceReceipt P event :=
  ⟨P.stepTrace event, rfl⟩

/-- Canonical adapter into the existing event-indexed native lifecycle. -/
def Authority.toNativeResidualUpdateProcess
    (P : Process.{u}) (A : Authority P) : NativeResidualUpdate.Process where
  Residual := P.State
  Content := A.Content
  Bearer := A.Bearer
  Scope := A.Scope
  Lineage := A.Lineage
  Incidence := A.Incidence
  SourceObservation := A.SourceObservation
  EventAt := P.EventAt
  ObstructionAt := A.ObstructionAt
  update := P.update
  content := A.content
  anchor := A.anchor
  incidence := A.incidence
  obstructionContent := A.obstructionContent
  obstructionResidual := A.obstructionState
  admissionBearer := A.admissionBearer
  nextBearer := A.nextBearer
  KeepAt := fun {_state} event => KeepReceipt P event
  TraceAt := fun {_state} event => TraceReceipt P event
  PathAt := fun {state} _event target => GeneratedPathAt P state target
  WriteBackAt := fun {_state} _event path => PathWriteBack P path
  RouteAt := fun {state} event oldBearer nextBearer =>
    A.RouteAt (state := state) event oldBearer nextBearer
  keepReceipt := keepReceipt P
  traceReceipt := traceReceipt P
  pathReceipt := fun {current} event =>
    .oneStep current event
  writeBackReceipt := fun {_current} _event =>
    GeneratedPathAt.writeBack _
  routeReceipt := A.routeReceipt
  content_update := A.content_update

abbrev NativeProcess (P : Process.{u}) (A : Authority P) :=
  A.toNativeResidualUpdateProcess P

def SourceEvent.toNative
    {P : Process.{u}} {A : Authority P} (source : SourceEvent P) :
    NativeResidualUpdate.SourceEvent (NativeProcess P A) :=
  ⟨source.state, source.event⟩

end SourceGeneratedFiniteEventIndexedResidualProcess
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
