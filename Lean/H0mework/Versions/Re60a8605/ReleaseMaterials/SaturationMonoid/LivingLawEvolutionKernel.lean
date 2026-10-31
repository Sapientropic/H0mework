import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.EffectiveResidualUpdateResponsibilityProcess
import H0mework.Foundation.Authority.Receipt
import H0mework.Foundation.Source.Anchor

/-!
# Living-law total evolution

Every reachable current must emit one source-owned disposition.  Ordinary
fixed-law progress may be unavailable, but the framework still generates a
relation write, continued transport, Borromean redirect, faithful terminal, or
an obstruction-driven law-surface extension which immediately recovers a
native write.

The carrier stores the process residual value with its state.  Bare carrier
types remain an ambient model presentation; actual current-atom authority also
requires the P7/P68/P98 recognition exported by
`LivingLawAtomFieldSeparation`.  Every continuing
disposition preserves the exact source anchor, incidence, law lineage, and law
surface.  Its target, typed path, trace, and write-back are generated from the
current surface's effective process, rather than supplied as receipt fields.
Law-surface extension is the only constructor allowed to change the surface
inside this fixed `K/E` carrier.  It exposes the obstruction, producer demand,
homogeneous whole-carrier translation, and revised current.  The revised
current must then re-enter the same raw-world compiler; no embedded first
write is accepted here.  This is the chart-local living-law layer, not the
reflexive U8 theory revision.  Constructive U6 accounts and U7 obstruction
demands live in `LivingLawRelationNetworkKernel`; Mathlib path transport is an
explicit downstream adapter, and full U8 expressibility-driven theory
evolution lives in `LivingLawTheoryEvolutionKernel`.

`Process.generatedHistory` records an on-the-nose `P.generate current`
equation at every public constructor, so there is no optional continuation or
caller-supplied prefix oracle.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution

open ResidualProjection
open EffectiveResidualUpdate

universe u

variable {K E : Type u}
variable [Field K] [AddCommGroup E] [Module K E]

/-- Carrier data shared by every revision of one living law surface. -/
structure Carrier where
  LawSurface : Type u
  State : LawSurface → Type u
  process : (surface : LawSurface) →
    EffectiveResidualProcess K E (State surface)
  Scope : Type u
  Lineage : Type u
  Incidence : Type u
  Bearer : Type u
  LawLineage : Type u
  SourceObservation : ComplementObservation.ComplementObservationCarrier.{u}

/-- A reachable model current contains the process residual value, not only a
state label, together with the exact public source and law-lineage account.
Its event authority is established by a source-native or causal producer;
legacy `NoSuspendedMagic` supplies only a compatibility readout.  Local-atom
authority is established separately by atom/field recognition. -/
structure Current (C : Carrier (K := K) (E := E)) where
  surface : C.LawSurface
  residual : ResidualState (C.process surface)
  anchor : MinimalRegistrableSourceAnchor
    C.SourceObservation C.Scope C.Lineage
  incidence : C.Incidence
  bearer : C.Bearer
  lawLineage : C.LawLineage

/-- Source-owned event, disposition, terminal, and law-revision grammar.

The vocabulary may recognize which kind of write an actual event performs,
but it cannot choose that event's target, path, trace, or write-back.  Those
are generated below from the effective process of the current law surface. -/
structure Vocabulary (C : Carrier (K := K) (E := E)) : Type (u + 1) where
  ActualEventAt : Current C → Type u
  eventAnchor : {current : Current C} → ActualEventAt current →
    MinimalRegistrableSourceAnchor C.SourceObservation C.Scope C.Lineage
  eventIncidence : {current : Current C} → ActualEventAt current → C.Incidence
  eventLawLineage : {current : Current C} → ActualEventAt current → C.LawLineage
  eventNextBearer : {current : Current C} → ActualEventAt current → C.Bearer
  RouteAcceptedAt : {current : Current C} → ActualEventAt current →
    C.Bearer → C.Bearer → Type u
  NativeWriteAt : {current : Current C} → ActualEventAt current → Type u
  RelationWriteAt : {current : Current C} → ActualEventAt current → Type u
  ContinuedTransportAt : {current : Current C} →
    ActualEventAt current → Type u
  BorromeanRedirectAt : {current : Current C} →
    ActualEventAt current → Type u
  TerminalEventAt : Current C → Type u
  terminalEventAnchor : {current : Current C} → TerminalEventAt current →
    MinimalRegistrableSourceAnchor C.SourceObservation C.Scope C.Lineage
  terminalEventIncidence : {current : Current C} → TerminalEventAt current →
    C.Incidence
  terminalEventLawLineage : {current : Current C} → TerminalEventAt current →
    C.LawLineage
  CompleteActualDescentAt : {current : Current C} → TerminalEventAt current →
    Type u
  FaithfulTerminalReceiptAt : {current : Current C} →
    TerminalEventAt current → Type u
  LawObstructionAt : Current C → Type u
  ProducerDemandAt : {current : Current C} → LawObstructionAt current → Type u
  ExtensionEventAt : Current C → Type u
  extensionEventAnchor : {current : Current C} → ExtensionEventAt current →
    MinimalRegistrableSourceAnchor C.SourceObservation C.Scope C.Lineage
  extensionEventIncidence : {current : Current C} → ExtensionEventAt current →
    C.Incidence
  extensionEventLawLineage : {current : Current C} → ExtensionEventAt current →
    C.LawLineage
  ExtensionRouteAcceptedAt : {current : Current C} →
    ExtensionEventAt current → C.Bearer → C.Bearer → Type u
  ExtensionDemandPaidAt : {current : Current C} →
    (event : ExtensionEventAt current) →
    (obstruction : LawObstructionAt current) →
    ProducerDemandAt obstruction → {revised : Current C} →
    ActualEventAt revised → Type u
  LawRevisionAt : {current : Current C} → (event : ExtensionEventAt current) →
    (obstruction : LawObstructionAt current) →
    ProducerDemandAt obstruction → Current C → Type u

/-- Homogeneous chart-local whole-process translation between two surfaces of
one fixed carrier.  State/update and residual/keep commute on the whole
carriers; injectivity prevents the translation from erasing a state or
residual kernel, and `current_state_eq` lands the exact old current at the
revised current.  This is U6-compatible transport data, not by itself a U8
theory-revision producer. -/
structure LawSurfaceTransportAt
    (C : Carrier (K := K) (E := E))
    (source target : Current C) : Type u where
  toState : C.State source.surface → C.State target.surface
  stateMap_injective : Function.Injective toState
  current_state_eq : toState source.residual.state = target.residual.state
  toResidual : E →ₗ[K] E
  residualMap_injective : Function.Injective toResidual
  residual_naturality : ∀ state,
    toResidual ((C.process source.surface).residual state) =
      (C.process target.surface).residual (toState state)
  update_commutes : ∀ state,
    toState ((C.process source.surface).update state) =
      (C.process target.surface).update (toState state)
  keep_commutes : ∀ residual,
    toResidual ((C.process source.surface).keep residual) =
      (C.process target.surface).keep (toResidual residual)

theorem LawSurfaceTransportAt.current_residual_eq
    {C : Carrier (K := K) (E := E)}
    {source target : Current C}
    (revision : LawSurfaceTransportAt C source target) :
    revision.toResidual source.residual.value =
      target.residual.value := by
  rw [source.residual.value_eq, target.residual.value_eq]
  rw [revision.residual_naturality, revision.current_state_eq]

/-- Trace commuting is forced by the same residual/keep square; it is not a
second revision certificate. -/
theorem LawSurfaceTransportAt.trace_commutes
    {C : Carrier (K := K) (E := E)}
    {source target : Current C}
    (revision : LawSurfaceTransportAt C source target)
    (residual : E) :
    revision.toResidual
        (AffineRelaxation.linearResidualTrace
          (C.process source.surface).keep residual) =
      AffineRelaxation.linearResidualTrace
        (C.process target.surface).keep
        (revision.toResidual residual) := by
  simp [AffineRelaxation.linearResidualTrace, revision.keep_commutes]

/-- The same commuting square lifts to the whole live/memory write-back
carrier. -/
theorem LawSurfaceTransportAt.writeBack_commutes
    {C : Carrier (K := K) (E := E)}
    {source target : Current C}
    (revision : LawSurfaceTransportAt C source target)
    (state : ResidualTraceWriteBackCarrier E) :
    residualTraceWriteBackMap revision.toResidual
        (residualTraceWriteBackKeep
          (C.process source.surface).keep state) =
      residualTraceWriteBackKeep
        (C.process target.surface).keep
        (residualTraceWriteBackMap revision.toResidual state) :=
  residualTraceWriteBackMap_keep_commutes
    revision.toResidual
    (C.process source.surface).keep
    (C.process target.surface).keep
    revision.keep_commutes
    state

/-- The whole-carrier transport data induces a genuine morphism of the two
native path theories.  This transports paths before any endpoint readout and
therefore strengthens the earlier state/residual commuting square to the U6
path level without adding another certificate field. -/
def LawSurfaceTransportAt.pathMorphism
    {C : Carrier (K := K) (E := E)}
    {source target : Current C}
    (revision : LawSurfaceTransportAt C source target) :
    PathIndexedResidualTransport.Morphism
      (C.process source.surface).toPathIndexedResidualTransport
      (C.process target.surface).toPathIndexedResidualTransport where
  quiverMap :=
    { obj := fun vertex =>
        (C.process target.surface).vertex
          (revision.toState vertex.state)
      map := by
        intro left right edge
        change (C.process source.surface).UpdateEdge left right at edge
        cases edge
        simpa [revision.update_commutes] using
          (C.process target.surface).updateEdge
            (revision.toState left.state) }
  carrierMap := revision.toResidual
  residual_naturality := fun vertex =>
    revision.residual_naturality vertex.state
  edge_keep_naturality := by
    intro left right edge residual
    exact revision.keep_commutes residual

/-- Every actual path trace survives the law-surface translation through the
same path morphism. -/
theorem LawSurfaceTransportAt.pathTrace_survives
    {C : Carrier (K := K) (E := E)}
    {source target : Current C}
    (revision : LawSurfaceTransportAt C source target)
    {left right : (C.process source.surface).UpdateVertex}
    (path : Quiver.Path left right) :
    revision.toResidual
        ((C.process source.surface).toPathIndexedResidualTransport.pathTrace
          path) =
      (C.process target.surface).toPathIndexedResidualTransport.pathTrace
        (revision.pathMorphism.mapPath path) :=
  revision.pathMorphism.pathTrace_naturality path

/-- Whole path-indexed write-back, not only the endpoint scalar, survives the
same revision. -/
theorem LawSurfaceTransportAt.pathWriteBack_survives
    {C : Carrier (K := K) (E := E)}
    {source target : Current C}
    (revision : LawSurfaceTransportAt C source target)
    {left right : (C.process source.surface).UpdateVertex}
    (path : Quiver.Path left right) :
    residualTraceWriteBackMap revision.toResidual
        ((C.process source.surface).toPathIndexedResidualTransport.pathWriteBack
          path) =
      (C.process target.surface).toPathIndexedResidualTransport.pathWriteBack
        (revision.pathMorphism.mapPath path) :=
  revision.pathMorphism.pathWriteBack_naturality path

/-- Bearer routing belongs to the exact event.  Retention is equality; a
change must carry an accepted route generated at that event. -/
inductive BearerDispositionAt
    {C : Carrier (K := K) (E := E)} (V : Vocabulary C)
    {current : Current C} (event : V.ActualEventAt current)
    (nextBearer : C.Bearer) : Type u
  | retained (eq : current.bearer = nextBearer) :
      BearerDispositionAt V event nextBearer
  | transferred
      (receipt : V.RouteAcceptedAt event current.bearer nextBearer) :
      BearerDispositionAt V event nextBearer

/-- A law revision cannot silently switch the bearer account.  Retention is
equality; a change must be accepted by the exact extension event. -/
inductive ExtensionBearerDispositionAt
    {C : Carrier (K := K) (E := E)} (V : Vocabulary C)
    {current : Current C} (event : V.ExtensionEventAt current)
    (nextBearer : C.Bearer) : Type u
  | retained (eq : current.bearer = nextBearer) :
      ExtensionBearerDispositionAt V event nextBearer
  | transferred
      (receipt : V.ExtensionRouteAcceptedAt event current.bearer nextBearer) :
      ExtensionBearerDispositionAt V event nextBearer

/-- Common source account of every nonterminal disposition.

There is deliberately no caller-supplied target, path, trace, or write-back.
The exact target is the current law surface's native update; the other three
objects are its canonical path-indexed projections. -/
structure GeneratedWriteAt
    {C : Carrier (K := K) (E := E)} (V : Vocabulary C)
    (current : Current C) : Type u where
  event : V.ActualEventAt current
  event_anchor_eq : V.eventAnchor event = current.anchor
  event_incidence_eq : V.eventIncidence event = current.incidence
  event_lawLineage_eq : V.eventLawLineage event = current.lawLineage
  update_ne_source :
    (C.process current.surface).update current.residual.state ≠
      current.residual.state
  bearerDisposition :
    BearerDispositionAt V event (V.eventNextBearer event)

namespace GeneratedWriteAt

variable {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
variable {current : Current C}

/-- The exact native target generated by the current surface's effective
process. -/
def next (write : GeneratedWriteAt V current) : Current C where
  surface := current.surface
  residual := residualState (C.process current.surface)
    ((C.process current.surface).update current.residual.state)
  anchor := current.anchor
  incidence := current.incidence
  bearer := V.eventNextBearer write.event
  lawLineage := current.lawLineage

/-- The same actual update's genuine one-edge native path. -/
def path (write : GeneratedWriteAt V current) :
    ActualUpdatePath (C.process current.surface)
      current.residual write.next.residual :=
  (C.process current.surface).updatePath current.residual.state 1

/-- The forced trace of the same native update. -/
def trace (_write : GeneratedWriteAt V current) :
    TraceReceipt (C.process current.surface) current.residual.state :=
  traceReceipt (C.process current.surface) current.residual.state

/-- Path-indexed write-back of the same native update. -/
def writeBack (write : GeneratedWriteAt V current) :
    WriteBackReceipt (C.process current.surface)
      current.residual write.next.residual write.path :=
  writeBackReceipt (C.process current.surface)
    current.residual write.next.residual write.path

@[simp] theorem next_state (write : GeneratedWriteAt V current) :
    write.next.residual.state =
      (C.process current.surface).update current.residual.state := by
  rfl

theorem next_state_ne (write : GeneratedWriteAt V current) :
    write.next.residual.state ≠ current.residual.state := by
  intro stutter
  exact write.update_ne_source (write.next_state.symm.trans stutter)

/-- A stuttering effective update has no inhabitant of any of the four write
branches.  Unchanged custody must be represented by an independently debited
maintenance event. -/
theorem not_nonempty_of_update_eq_source
    (stutter : (C.process current.surface).update current.residual.state =
      current.residual.state) :
    ¬ Nonempty (GeneratedWriteAt V current) := by
  rintro ⟨write⟩
  exact write.update_ne_source stutter

@[simp] theorem next_anchor_eq (write : GeneratedWriteAt V current) :
    write.next.anchor = current.anchor := by
  rfl

@[simp] theorem next_incidence_eq (write : GeneratedWriteAt V current) :
    write.next.incidence = current.incidence := by
  rfl

@[simp] theorem next_lawLineage_eq (write : GeneratedWriteAt V current) :
    write.next.lawLineage = current.lawLineage := by
  rfl

@[simp] theorem next_surface_eq (write : GeneratedWriteAt V current) :
    write.next.surface = current.surface := by
  rfl

end GeneratedWriteAt

/-- A terminal is an actual classified event after complete descent, not the
absence of an ordinary progress event. -/
structure GeneratedFaithfulTerminalAt
    {C : Carrier (K := K) (E := E)} (V : Vocabulary C)
    (current : Current C) : Type u where
  event : V.TerminalEventAt current
  event_anchor_eq : V.terminalEventAnchor event = current.anchor
  event_incidence_eq : V.terminalEventIncidence event = current.incidence
  event_lawLineage_eq : V.terminalEventLawLineage event = current.lawLineage
  completeActualDescent : V.CompleteActualDescentAt event
  noOutgoingWrite : IsEmpty (V.ActualEventAt current)
  receipt : V.FaithfulTerminalReceiptAt event

/-- A law-surface obstruction emits a demand and changes the chart-local
surface under the same source account.  Recovery is not stored here: the
revised current must be fed back to the same canonical generator, whose next
result is audited by the raw-world realization layer.  Since `K`, `E`, and the
carrier remain fixed, this is not the reflexive U8 step which revises the
theory language itself. -/
structure GeneratedLawSurfaceExtensionAt
    {C : Carrier (K := K) (E := E)} (V : Vocabulary C)
    (current : Current C) : Type u where
  event : V.ExtensionEventAt current
  event_anchor_eq : V.extensionEventAnchor event = current.anchor
  event_incidence_eq : V.extensionEventIncidence event = current.incidence
  event_lawLineage_eq : V.extensionEventLawLineage event = current.lawLineage
  obstruction : V.LawObstructionAt current
  demand : V.ProducerDemandAt obstruction
  revised : Current C
  surface_changed : revised.surface ≠ current.surface
  revised_anchor_eq : revised.anchor = current.anchor
  revised_incidence_eq : revised.incidence = current.incidence
  revised_lawLineage_eq : revised.lawLineage = current.lawLineage
  revised_bearerDisposition :
    ExtensionBearerDispositionAt V event revised.bearer
  surfaceTransport : LawSurfaceTransportAt C current revised
  revision : V.LawRevisionAt event obstruction demand revised

/-- Mandatory living-law disposition at one reachable current. -/
inductive GeneratedEvolutionAt
    {C : Carrier (K := K) (E := E)} (V : Vocabulary C) :
    Current C → Type u
  | nativeWrite {current : Current C} (write : GeneratedWriteAt V current)
      (receipt : V.NativeWriteAt write.event) :
      GeneratedEvolutionAt V current
  | relationWrite {current : Current C} (write : GeneratedWriteAt V current)
      (receipt : V.RelationWriteAt write.event) :
      GeneratedEvolutionAt V current
  | continuedTransport {current : Current C}
      (write : GeneratedWriteAt V current)
      (receipt : V.ContinuedTransportAt write.event) :
      GeneratedEvolutionAt V current
  | borromeanRedirect {current : Current C}
      (write : GeneratedWriteAt V current)
      (receipt : V.BorromeanRedirectAt write.event) :
      GeneratedEvolutionAt V current
  | faithfulTerminal {current : Current C}
      (terminal : GeneratedFaithfulTerminalAt V current) :
      GeneratedEvolutionAt V current
  | lawSurfaceExtension {current : Current C}
      (extension : GeneratedLawSurfaceExtensionAt V current) :
      GeneratedEvolutionAt V current

/-- Public actual-event view of a generated disposition. -/
inductive EvolutionEventAt
    {C : Carrier (K := K) (E := E)} (V : Vocabulary C)
    (current : Current C) : Type u
  | write (event : V.ActualEventAt current)
  | terminal (event : V.TerminalEventAt current)
  | extension (event : V.ExtensionEventAt current)

def EvolutionEventAt.anchor
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {current : Current C} : EvolutionEventAt V current →
    MinimalRegistrableSourceAnchor C.SourceObservation C.Scope C.Lineage
  | .write event => V.eventAnchor event
  | .terminal event => V.terminalEventAnchor event
  | .extension event => V.extensionEventAnchor event

def EvolutionEventAt.incidence
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {current : Current C} : EvolutionEventAt V current → C.Incidence
  | .write event => V.eventIncidence event
  | .terminal event => V.terminalEventIncidence event
  | .extension event => V.extensionEventIncidence event

def EvolutionEventAt.lawLineage
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {current : Current C} : EvolutionEventAt V current → C.LawLineage
  | .write event => V.eventLawLineage event
  | .terminal event => V.terminalEventLawLineage event
  | .extension event => V.extensionEventLawLineage event

def GeneratedEvolutionAt.event
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {current : Current C} :
    GeneratedEvolutionAt V current → EvolutionEventAt V current
  | .nativeWrite write _ => .write write.event
  | .relationWrite write _ => .write write.event
  | .continuedTransport write _ => .write write.event
  | .borromeanRedirect write _ => .write write.event
  | .faithfulTerminal terminal => .terminal terminal.event
  | .lawSurfaceExtension extension => .extension extension.event

theorem GeneratedEvolutionAt.event_anchor_eq
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {current : Current C} (evolution : GeneratedEvolutionAt V current) :
    evolution.event.anchor = current.anchor := by
  cases evolution with
  | nativeWrite write receipt => exact write.event_anchor_eq
  | relationWrite write receipt => exact write.event_anchor_eq
  | continuedTransport write receipt => exact write.event_anchor_eq
  | borromeanRedirect write receipt => exact write.event_anchor_eq
  | faithfulTerminal terminal => exact terminal.event_anchor_eq
  | lawSurfaceExtension extension => exact extension.event_anchor_eq

theorem GeneratedEvolutionAt.event_incidence_eq
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {current : Current C} (evolution : GeneratedEvolutionAt V current) :
    evolution.event.incidence = current.incidence := by
  cases evolution with
  | nativeWrite write receipt => exact write.event_incidence_eq
  | relationWrite write receipt => exact write.event_incidence_eq
  | continuedTransport write receipt => exact write.event_incidence_eq
  | borromeanRedirect write receipt => exact write.event_incidence_eq
  | faithfulTerminal terminal => exact terminal.event_incidence_eq
  | lawSurfaceExtension extension => exact extension.event_incidence_eq

theorem GeneratedEvolutionAt.event_lawLineage_eq
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {current : Current C} (evolution : GeneratedEvolutionAt V current) :
    evolution.event.lawLineage = current.lawLineage := by
  cases evolution with
  | nativeWrite write receipt => exact write.event_lawLineage_eq
  | relationWrite write receipt => exact write.event_lawLineage_eq
  | continuedTransport write receipt => exact write.event_lawLineage_eq
  | borromeanRedirect write receipt => exact write.event_lawLineage_eq
  | faithfulTerminal terminal => exact terminal.event_lawLineage_eq
  | lawSurfaceExtension extension => exact extension.event_lawLineage_eq

/-- Framework-level local totality: the source emits an event at every
reachable current and its shared compiler returns a disposition carrying that
exact event.  This structure generates local evolution but issues no world
authority; world effects require registration at a fixed root occurrence. -/
structure Process
    {C : Carrier (K := K) (E := E)} (V : Vocabulary C) : Type (u + 1) where
  EmittedEventAt : Current C → Type u
  emit : (current : Current C) → EmittedEventAt current
  eventView : {current : Current C} → EmittedEventAt current →
    EvolutionEventAt V current
  compile : {current : Current C} → EmittedEventAt current →
    GeneratedEvolutionAt V current
  compile_event_eq : {current : Current C} → (event : EmittedEventAt current) →
    (compile event).event = eventView event

def Process.generate
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    (P : Process V) (current : Current C) : GeneratedEvolutionAt V current :=
  P.compile (P.emit current)

theorem Process.generatedEvolution_event_eq_emit
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    (P : Process V) (current : Current C) :
    (P.generate current).event = P.eventView (P.emit current) :=
  P.compile_event_eq (P.emit current)

/-- Source-owned fixed-law native totality is a strong specialization, not an
optional premise of the living framework. -/
structure FixedLawNativeTotal
    {C : Carrier (K := K) (E := E)} (V : Vocabulary C) : Type (u + 1) where
  write : (current : Current C) → GeneratedWriteAt V current
  native : (current : Current C) →
    V.NativeWriteAt (write current).event

def FixedLawNativeTotal.toProcess
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    (T : FixedLawNativeTotal V) : Process V where
  EmittedEventAt := fun current =>
    { event : V.ActualEventAt current // event = (T.write current).event }
  emit := fun current => ⟨(T.write current).event, rfl⟩
  eventView := fun event => .write event.val
  compile := fun {current} _ =>
    .nativeWrite (T.write current) (T.native current)
  compile_event_eq := by
    intro current event
    change EvolutionEventAt.write (T.write current).event =
      EvolutionEventAt.write event.val
    exact congrArg EvolutionEventAt.write event.property.symm

/-- Dependent generated history certified step-by-step by the same process.

Every public constructor carries the on-the-nose equation identifying its
head with `P.generate current`.  Thus `P` is not a phantom index and callers
cannot splice a parallel history.  A surface extension continues at the exact
revised current; it does not execute a stored first write behind the revised
compiler's back. -/
inductive GeneratedHistory
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    (P : Process V) : (current : Current C) → Nat → Type u
  | zero (current : Current C) : GeneratedHistory P current 0
  | nativeWrite {current : Current C} {fuel : Nat}
      (write : GeneratedWriteAt V current)
      (receipt : V.NativeWriteAt write.event)
      (generated_eq : P.generate current = .nativeWrite write receipt)
      (tail : GeneratedHistory P write.next fuel) :
      GeneratedHistory P current (fuel + 1)
  | relationWrite {current : Current C} {fuel : Nat}
      (write : GeneratedWriteAt V current)
      (receipt : V.RelationWriteAt write.event)
      (generated_eq : P.generate current = .relationWrite write receipt)
      (tail : GeneratedHistory P write.next fuel) :
      GeneratedHistory P current (fuel + 1)
  | continuedTransport {current : Current C} {fuel : Nat}
      (write : GeneratedWriteAt V current)
      (receipt : V.ContinuedTransportAt write.event)
      (generated_eq : P.generate current = .continuedTransport write receipt)
      (tail : GeneratedHistory P write.next fuel) :
      GeneratedHistory P current (fuel + 1)
  | borromeanRedirect {current : Current C} {fuel : Nat}
      (write : GeneratedWriteAt V current)
      (receipt : V.BorromeanRedirectAt write.event)
      (generated_eq : P.generate current = .borromeanRedirect write receipt)
      (tail : GeneratedHistory P write.next fuel) :
      GeneratedHistory P current (fuel + 1)
  | faithfulTerminal {current : Current C} {fuel : Nat}
      (terminal : GeneratedFaithfulTerminalAt V current)
      (generated_eq : P.generate current = .faithfulTerminal terminal) :
      GeneratedHistory P current (fuel + 1)
  | lawSurfaceExtension {current : Current C} {fuel : Nat}
      (extension : GeneratedLawSurfaceExtensionAt V current)
      (generated_eq : P.generate current = .lawSurfaceExtension extension)
      (tail : GeneratedHistory P extension.revised fuel) :
      GeneratedHistory P current (fuel + 1)

namespace GeneratedHistory

/-- Head disposition recorded by a positive-fuel history. -/
def head
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {P : Process V} {current : Current C} {fuel : Nat} :
    GeneratedHistory P current (fuel + 1) → GeneratedEvolutionAt V current
  | .nativeWrite write receipt _ _ => .nativeWrite write receipt
  | .relationWrite write receipt _ _ => .relationWrite write receipt
  | .continuedTransport write receipt _ _ =>
      .continuedTransport write receipt
  | .borromeanRedirect write receipt _ _ =>
      .borromeanRedirect write receipt
  | .faithfulTerminal terminal _ => .faithfulTerminal terminal
  | .lawSurfaceExtension extension _ _ => .lawSurfaceExtension extension

/-- No-Free Continuation: the head of every public history is the exact
disposition emitted by the indexed process at that current. -/
theorem head_eq_generate
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {P : Process V} {current : Current C} {fuel : Nat}
    (history : GeneratedHistory P current (fuel + 1)) :
    history.head = P.generate current := by
  cases history with
  | nativeWrite write receipt generated_eq tail => exact generated_eq.symm
  | relationWrite write receipt generated_eq tail => exact generated_eq.symm
  | continuedTransport write receipt generated_eq tail =>
      exact generated_eq.symm
  | borromeanRedirect write receipt generated_eq tail =>
      exact generated_eq.symm
  | faithfulTerminal terminal generated_eq => exact generated_eq.symm
  | lawSurfaceExtension extension generated_eq tail =>
      exact generated_eq.symm

end GeneratedHistory

/-- Pure-native fixed-law projection of the living execution kernel.  Every
successor starts at the exact target selected by the same source-owned total
producer; a caller cannot splice independently admitted finite runs. -/
inductive GeneratedPrefix
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    (T : FixedLawNativeTotal V) : (current : Current C) → Nat → Type u
  | zero (current : Current C) : GeneratedPrefix T current 0
  | step {current : Current C} {length : Nat}
      (tail : GeneratedPrefix T (T.write current).next length) :
      GeneratedPrefix T current (length + 1)

namespace GeneratedPrefix

/-- Exact target reached by this one-admission native prefix. -/
def target
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {T : FixedLawNativeTotal V} {current : Current C} {length : Nat} :
    GeneratedPrefix T current length → Current C
  | .zero current => current
  | .step tail => tail.target

/-- The fixed-law prefix is the pure-native fragment of the general living
history, with the same event/path/write-back payload at every step. -/
def toHistory
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {T : FixedLawNativeTotal V} {current : Current C} {length : Nat}
    (generated : GeneratedPrefix T current length) :
    GeneratedHistory T.toProcess current length :=
  match generated with
  | .zero current => .zero current
  | .step tail =>
      .nativeWrite (T.write current) (T.native current) rfl tail.toHistory

theorem target_anchor_eq
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {T : FixedLawNativeTotal V} {current : Current C} {length : Nat}
    (generated : GeneratedPrefix T current length) :
    generated.target.anchor = current.anchor := by
  induction generated with
  | zero => rfl
  | step tail inductionHypothesis =>
      exact inductionHypothesis.trans (T.write _).next_anchor_eq

theorem target_incidence_eq
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {T : FixedLawNativeTotal V} {current : Current C} {length : Nat}
    (generated : GeneratedPrefix T current length) :
    generated.target.incidence = current.incidence := by
  induction generated with
  | zero => rfl
  | step tail inductionHypothesis =>
      exact inductionHypothesis.trans (T.write _).next_incidence_eq

theorem target_lawLineage_eq
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {T : FixedLawNativeTotal V} {current : Current C} {length : Nat}
    (generated : GeneratedPrefix T current length) :
    generated.target.lawLineage = current.lawLineage := by
  induction generated with
  | zero => rfl
  | step tail inductionHypothesis =>
      exact inductionHypothesis.trans (T.write _).next_lawLineage_eq

theorem target_surface_eq
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    {T : FixedLawNativeTotal V} {current : Current C} {length : Nat}
    (generated : GeneratedPrefix T current length) :
    generated.target.surface = current.surface := by
  induction generated with
  | zero => rfl
  | step tail inductionHypothesis =>
      exact inductionHypothesis.trans (T.write _).next_surface_eq

end GeneratedPrefix

/-- Every fixed-law total producer generates arbitrary exact-target prefixes
from the supplied current; `Total` is not exposed as a theorem premise. -/
def FixedLawNativeTotal.generatedPrefix
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    (T : FixedLawNativeTotal V) : (current : Current C) → (length : Nat) →
      GeneratedPrefix T current length
  | current, 0 => .zero current
  | current, length + 1 =>
      .step (T.generatedPrefix (T.write current).next length)

def Process.generatedHistory
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    (P : Process V) : (current : Current C) → (fuel : Nat) →
      GeneratedHistory P current fuel
  | current, 0 => .zero current
  | current, fuel + 1 =>
      match generated_eq : P.generate current with
      | .nativeWrite write receipt =>
          .nativeWrite write receipt generated_eq
            (P.generatedHistory write.next fuel)
      | .relationWrite write receipt =>
          .relationWrite write receipt generated_eq
            (P.generatedHistory write.next fuel)
      | .continuedTransport write receipt =>
          .continuedTransport write receipt generated_eq
            (P.generatedHistory write.next fuel)
      | .borromeanRedirect write receipt =>
          .borromeanRedirect write receipt generated_eq
            (P.generatedHistory write.next fuel)
      | .faithfulTerminal terminal =>
          .faithfulTerminal terminal generated_eq
      | .lawSurfaceExtension extension =>
          .lawSurfaceExtension extension generated_eq
            (P.generatedHistory extension.revised fuel)

theorem FixedLawNativeTotal.generatedPrefix_toHistory_eq_generatedHistory
    {C : Carrier (K := K) (E := E)} {V : Vocabulary C}
    (T : FixedLawNativeTotal V) (current : Current C) (length : Nat) :
    (T.generatedPrefix current length).toHistory =
      T.toProcess.generatedHistory current length := by
  induction length generalizing current with
  | zero => rfl
  | succ length inductionHypothesis =>
      simp only [FixedLawNativeTotal.generatedPrefix,
        GeneratedPrefix.toHistory, Process.generatedHistory]
      rw [inductionHypothesis]
      rfl

end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
