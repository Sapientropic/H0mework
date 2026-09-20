import H0mework.Foundation.Semantics.KernelPair
import H0mework.Foundation.Responsibility.Lifecycle

/-!
# Consumer-relative responsibility observers

A thin observation is safe only relative to a specific downstream consumer.
This module keeps the three outcomes separate:

* `certifiedSafe`: the consumer factors through the observation;
* `hidden`: one actual fiber contains different required dispositions;
* `unclassified`: no default may reinterpret the boundary as safe.

The concrete responsibility observers below are derived from lifecycle state.
No observer Boolean is stored as a source field.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle

universe u v w x

/-- A consumer is safe on an observer exactly when it is constant on every
observer fiber. -/
def ConsumerSafe
    {State : Type u} {Observation : Type v} {Disposition : Type w}
    (observe : State → Observation) (consumer : State → Disposition) : Prop :=
  ∀ {left right : State},
    observe left = observe right → consumer left = consumer right

/-- Actual witness that a thin observer hides a distinction required by one
consumer. -/
structure HiddenNullWitness
    {State : Type u} {Observation : Type v} {Disposition : Type w}
    (observe : State → Observation) (consumer : State → Disposition) : Type u where
  left : State
  right : State
  sameObservation : observe left = observe right
  differentDisposition : consumer left ≠ consumer right

/-- Unknown remains an explicit boundary, not a default-safe branch. -/
inductive ConsumerKernelStatus
    {State : Type u} {Observation : Type v} {Disposition : Type w}
    (observe : State → Observation) (consumer : State → Disposition) : Type (max u v w)
  | certifiedSafe (receipt : ConsumerSafe observe consumer)
  | hidden (witness : HiddenNullWitness observe consumer)
  | unclassified

namespace ConsumerSafe

theorem of_factorization
    {State : Type u} {Observation : Type v} {Disposition : Type w}
    {observe : State → Observation} {consumer : State → Disposition}
    (factor : Observation → Disposition)
    (commutes : ∀ state, factor (observe state) = consumer state) :
    ConsumerSafe observe consumer := by
  intro left right sameObservation
  rw [← commutes left, ← commutes right, sameObservation]

theorem postcompose
    {State : Type u} {Observation : Type v}
    {Disposition : Type w} {Projected : Type x}
    {observe : State → Observation} {consumer : State → Disposition}
    (safe : ConsumerSafe observe consumer) (project : Disposition → Projected) :
    ConsumerSafe observe (project ∘ consumer) := by
  intro left right sameObservation
  exact congrArg project (safe sameObservation)

/-- If a coarser safe observation factors through a refinement, the refined
observer is safe for the same consumer. -/
theorem of_refinement
    {State : Type u} {Coarse : Type v} {Fine : Type w}
    {Disposition : Type x}
    {coarse : State → Coarse} {fine : State → Fine}
    {consumer : State → Disposition}
    (safe : ConsumerSafe coarse consumer)
    (forget : Fine → Coarse)
    (factors : ∀ state, forget (fine state) = coarse state) :
    ConsumerSafe fine consumer := by
  intro left right sameFine
  apply safe
  rw [← factors left, ← factors right, sameFine]

end ConsumerSafe

namespace HiddenNullWitness

theorem not_consumerSafe
    {State : Type u} {Observation : Type v} {Disposition : Type w}
    {observe : State → Observation} {consumer : State → Disposition}
    (witness : HiddenNullWitness observe consumer) :
    ¬ ConsumerSafe observe consumer := by
  intro safe
  exact witness.differentDisposition (safe witness.sameObservation)

/-- Coarsening an already-hidden observation cannot repair its hidden fiber. -/
def coarsen
    {State : Type u} {Observation : Type v} {Coarse : Type w}
    {Disposition : Type x}
    {observe : State → Observation} {consumer : State → Disposition}
    (witness : HiddenNullWitness observe consumer) (project : Observation → Coarse) :
    HiddenNullWitness (project ∘ observe) consumer where
  left := witness.left
  right := witness.right
  sameObservation := congrArg project witness.sameObservation
  differentDisposition := witness.differentDisposition

end HiddenNullWitness

namespace ConsumerKernelStatus

def IsCertifiedSafe
    {State : Type u} {Observation : Type v} {Disposition : Type w}
    {observe : State → Observation} {consumer : State → Disposition} :
    ConsumerKernelStatus observe consumer → Prop
  | .certifiedSafe _ => True
  | .hidden _ => False
  | .unclassified => False

theorem unclassified_not_certifiedSafe
    {State : Type u} {Observation : Type v} {Disposition : Type w}
    {observe : State → Observation} {consumer : State → Disposition} :
    ¬ (ConsumerKernelStatus.unclassified :
      ConsumerKernelStatus observe consumer).IsCertifiedSafe := by
  simp [IsCertifiedSafe]

theorem hidden_not_certifiedSafe
    {State : Type u} {Observation : Type v} {Disposition : Type w}
    {observe : State → Observation} {consumer : State → Disposition}
    (witness : HiddenNullWitness observe consumer) :
    ¬ (ConsumerKernelStatus.hidden witness).IsCertifiedSafe := by
  simp [IsCertifiedSafe]

end ConsumerKernelStatus

/-- Full current-responsibility observer.  It is derived from stable slots and
retains the exact live obligation, including its admission source event,
anchor, incidence, scope, lineage, bearer, and residual.  Thin projections
may forget these fields only under the consumer-kernel audit below. -/
def currentResponsibilityObserver
    {V : Vocabulary} (state : ResponsibilityState V) :
    List (Option (AdmittedObligation V)) :=
  state.slots.map fun slot =>
    match slot with
    | .live obligation => some obligation
    | .terminal _ => none

/-- Scope observer is intentionally thin: invisible obligations are omitted,
so its exact kernel can be audited against the full observer. -/
structure ScopeObserver (V : Vocabulary) where
  visible : V.Scope → Bool

def ScopeObserver.observe
    {V : Vocabulary} (observer : ScopeObserver V)
    (state : ResponsibilityState V) : List V.Lineage :=
  state.slots.filterMap fun slot =>
    match slot with
    | .live obligation =>
        if observer.visible obligation.scope then some obligation.lineage else none
    | .terminal _ => none

namespace NativeResponsibilityProcess

variable {V : Vocabulary.{u}} (P : NativeResponsibilityProcess V)

/-- Actual admission cannot be confused with its source state by the full
current-responsibility observer. -/
theorem admit_currentResponsibilityObserver_ne
    {source : ResponsibilityState V} (event : P.AdmissionEvent) :
    currentResponsibilityObserver
        (Edge.admit (P := P) event : P.Edge source).target ≠
      currentResponsibilityObserver source := by
  intro equal
  have length_equal := congrArg List.length equal
  simp [currentResponsibilityObserver, Edge.target] at length_equal

theorem admit_not_currentResponsibilityKernel
    {source : ResponsibilityState V} (event : P.AdmissionEvent) :
    ¬ KernelPair currentResponsibilityObserver
      (Edge.admit (P := P) event : P.Edge source).target source :=
  admit_currentResponsibilityObserver_ne (P := P) event

theorem scopeObserver_observe_admit_of_invisible
    (observer : ScopeObserver V)
    {source : ResponsibilityState V} (event : P.AdmissionEvent)
    (invisible : observer.visible (P.admissionPayload event).scope = false) :
    observer.observe (Edge.admit (P := P) event : P.Edge source).target =
      observer.observe source := by
  simp [ScopeObserver.observe, Edge.target,
    NativeAdmissionPayload.toObligation, invisible]

/-- An invisible actual admission generates an exact hidden-NULL witness for
the thin scope observer, together with the full responsibility distinction. -/
def scopeObserver_invisibleAdmissionHiddenNull
    (observer : ScopeObserver V)
    {source : ResponsibilityState V} (event : P.AdmissionEvent)
    (invisible : observer.visible (P.admissionPayload event).scope = false) :
    HiddenNullWitness observer.observe currentResponsibilityObserver where
  left := (Edge.admit (P := P) event : P.Edge source).target
  right := source
  sameObservation :=
    scopeObserver_observe_admit_of_invisible P observer event invisible
  differentDisposition := admit_currentResponsibilityObserver_ne (P := P) event

/-- Source-backed redirect retained when a thin observer hides an admission.
It packages the actual edge rather than claiming that the thin carrier has
already been refined. -/
structure FullTraceRedirect
    (observer : ScopeObserver V) (source : ResponsibilityState V) : Type u where
  event : P.AdmissionEvent
  invisible : observer.visible (P.admissionPayload event).scope = false
  hidden : HiddenNullWitness observer.observe currentResponsibilityObserver
  hidden_eq : hidden =
    scopeObserver_invisibleAdmissionHiddenNull P observer
      (source := source) event invisible

def scopeObserver_invisibleAdmissionFullTraceRedirect
    (observer : ScopeObserver V)
    {source : ResponsibilityState V} (event : P.AdmissionEvent)
    (invisible : observer.visible (P.admissionPayload event).scope = false) :
    FullTraceRedirect P observer source where
  event := event
  invisible := invisible
  hidden := scopeObserver_invisibleAdmissionHiddenNull P observer
    (source := source) event invisible
  hidden_eq := rfl

/-- Observer trace generated from an exact lifecycle run.  Thin observers may
collapse individual edges, but they cannot reorder or invent them. -/
inductive ObserverTrace
    {Observation : Type v} (observe : ResponsibilityState V → Observation) :
    Observation → Observation → Type (max u v)
  | nil (state : ResponsibilityState V) : ObserverTrace observe (observe state) (observe state)
  | step {source middle : ResponsibilityState V}
      (prior : ObserverTrace observe (observe source) (observe middle))
      (edge : P.Edge middle) :
      ObserverTrace observe (observe source) (observe edge.target)

def Run.toObserverTrace
    {Observation : Type v} (observe : ResponsibilityState V → Observation)
    {source target : ResponsibilityState V} (run : P.Run source target) :
    P.ObserverTrace observe (observe source) (observe target) :=
  match run with
  | .nil => .nil source
  | .step prior edge => .step (prior.toObserverTrace observe) edge

def Run.toScopeObserverTrace
    (observer : ScopeObserver V)
    {source target : ResponsibilityState V} (run : P.Run source target) :
    P.ObserverTrace observer.observe (observer.observe source) (observer.observe target) :=
  NativeResponsibilityProcess.Run.toObserverTrace P observer.observe run

end NativeResponsibilityProcess

end ResponsibilityLifecycle
end SaturationMonoid
