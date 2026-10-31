import H0mework.Foundation.Authority.Receipt
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.EffectiveResidualProcessPathIndexedTransport
import H0mework.Realization.Residual.NativeResponsibility
import H0mework.Realization.Residual.Process

/-!
# Effective residual updates generate authoritative lifecycle progress

This module closes the receipt-authority gap of the generic responsibility
lifecycle.  Domain data is deliberately restricted to thin recognition of an
already existing `EffectiveResidualProcess`.  It cannot supply an update,
keep, forced trace, path, write-back, progress receipt, or lifecycle edge.

The shared constructor derives all of those from the same actual process
state and exposes legal progress as exactly the image of that constructor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace EffectiveResidualUpdate

open ResidualProjection
open AffineRelaxation

universe u

variable {K E State : Type u}
variable [Field K] [AddCommGroup E] [Module K E]

/-- A process state paired with the actual residual value owned by the same
effective process.  The equality prevents a domain adapter from changing the
responsibility residual while retaining the source-state label. -/
@[ext]
structure ResidualState
    (P : EffectiveResidualProcess K E State) : Type u where
  state : State
  value : E
  value_eq : value = P.residual state

/-- Canonical insertion of an effective-process state into the live residual
carrier. -/
def residualState
    (P : EffectiveResidualProcess K E State) (state : State) :
    ResidualState P :=
  ⟨state, P.residual state, rfl⟩

@[simp] theorem residualState_state
    (P : EffectiveResidualProcess K E State) (state : State) :
    (residualState P state).state = state := by
  rfl

@[simp] theorem residualState_value
    (P : EffectiveResidualProcess K E State) (state : State) :
    (residualState P state).value = P.residual state := by
  rfl

/-- Actual emitted ordinary progress events of one fixed effective process.
The fibre may be empty relative to this law surface; living-law evolution must
then generate a faithful terminal, another legal disposition, or a surface
extension.  Stuttering updates are deliberately excluded here; unchanged
custody belongs to the independently debited maintenance lifecycle. -/
structure ActualProgressSource
    (P : EffectiveResidualProcess K E State) : Type (u + 1) where
  Event : Type u
  Scope : Type u
  Lineage : Type u
  Incidence : Type u
  SourceObservation : ComplementObservation.ComplementObservationCarrier.{u}
  source : Event → State
  anchor : Event → MinimalRegistrableSourceAnchor
    SourceObservation Scope Lineage
  incidence : Event → Incidence
  update_ne_source : (event : Event) → P.update (source event) ≠ source event

/-- Exact source fibre of globally emitted actual events. -/
def ActualProgressSource.EventAt
    {P : EffectiveResidualProcess K E State}
    (S : ActualProgressSource P) (state : State) : Type u :=
  { event : S.Event // S.source event = state }

/-- This fixed law surface emits no ordinary progress event at the state.  It
is not by itself a faithful terminal receipt for the living framework. -/
abbrev ActualProgressSource.TerminalAt
    {P : EffectiveResidualProcess K E State}
    (S : ActualProgressSource P) (state : State) :=
  IsEmpty (S.EventAt state)

theorem ActualProgressSource.not_terminal_of_event
    {P : EffectiveResidualProcess K E State}
    (S : ActualProgressSource P) {state : State}
    (event : S.EventAt state) : ¬ S.TerminalAt state := by
  intro terminal
  exact terminal.false event

/-- A source-owned actual event at every effective-process state, all on the
same O0 anchor and incidence as one emitted origin. This is the exact extra
law needed for arbitrary finite prefixes; no target, path, trace, write-back,
or lifecycle outcome is a field. -/
structure ActualProgressSource.TotalAt
    {P : EffectiveResidualProcess K E State}
    (S : ActualProgressSource P) (origin : S.Event) : Type u where
  eventAt : (state : State) → S.EventAt state
  anchor_eq : (state : State) →
    S.anchor (eventAt state).1 = S.anchor origin
  incidence_eq : (state : State) →
    S.incidence (eventAt state).1 = S.incidence origin

/-- Domain recognition of an existing effective update.  There is no update,
receipt, path, write-back, target, or branch field. -/
structure Recognition
    (P : EffectiveResidualProcess K E State) : Type (u + 1) where
  Content : Type u
  Bearer : Type u
  ObstructionAt : State → Type u
  content : State → Content
  obstructionContent : {state : State} → ObstructionAt state → Content
  obstructionResidual : {state : State} → ObstructionAt state → State
  admissionBearer : State → Bearer
  nextBearer : State → Bearer
  RouteAt : State → Bearer → Bearer → Type u
  routeReceipt : (state : State) → (oldBearer : Bearer) →
    RouteAt state oldBearer (nextBearer state)
  content_update : (state : State) → content (P.update state) = content state

/-- The actual keep law, including its canonical typed-edge incarnation. -/
structure KeepReceipt
    (P : EffectiveResidualProcess K E State) (state : State) : Type u where
  residual_transport :
    P.residual (P.update state) = P.keep (P.residual state)
  typed_update :
    P.toPathIndexedResidualTransport.residual
          (P.vertex (P.update state)) =
      P.toPathIndexedResidualTransport.edgeKeep
        (P.updateEdge state)
        (P.toPathIndexedResidualTransport.residual (P.vertex state))

def keepReceipt
    (P : EffectiveResidualProcess K E State) (state : State) :
    KeepReceipt P state :=
  ⟨P.residual_transport_law state,
    P.pathIndexedResidualTransport_actual_update state⟩

/-- The uniquely forced complement and path-indexed write-back of the same
actual update. -/
structure TraceReceipt
    (P : EffectiveResidualProcess K E State) (state : State) : Type u where
  forcedTrace : E
  forcedTrace_eq :
    forcedTrace = linearResidualTrace P.keep (P.residual state)
  residual_split :
    P.residual state = P.residual (P.update state) + forcedTrace
  trace_unique : ∀ trace : E,
    P.residual state = P.residual (P.update state) + trace ↔
      trace = forcedTrace
  path_trace :
    P.toPathIndexedResidualTransport.pathTrace
        (P.updatePath state 1) = forcedTrace

def traceReceipt
    (P : EffectiveResidualProcess K E State) (state : State) :
    TraceReceipt P state where
  forcedTrace := linearResidualTrace P.keep (P.residual state)
  forcedTrace_eq := rfl
  residual_split :=
    effectiveProcess_residual_eq_next_residual_add_trace P state
  trace_unique := effectiveProcess_trace_unique P state
  path_trace := by
    rw [P.updatePath_pathTrace_eq, P.pathTrace_one]

/-- Genuine native paths between process-owned live residual states. -/
abbrev ActualUpdatePath
    (P : EffectiveResidualProcess K E State)
    (source target : ResidualState P) : Type u :=
  Quiver.Path (P.vertex source.state) (P.vertex target.state)

/-- Write-back is indexed by the exact native path that generated it.  It is
not an independently supplied pair which merely agrees with endpoint scalars. -/
structure WriteBackReceipt
    (P : EffectiveResidualProcess K E State)
    (source target : ResidualState P)
    (path : ActualUpdatePath P source target) : Type u where
  value : ResidualTraceWriteBackCarrier E
  value_eq : value = P.toPathIndexedResidualTransport.pathWriteBack path
  live_eq : value.1 = target.value
  trace_eq : value.2 = P.toPathIndexedResidualTransport.pathTrace path
  recollects_source :
    residualTraceWriteBackRecollection (K := K) value = source.value

def writeBackReceipt
    (P : EffectiveResidualProcess K E State)
    (source target : ResidualState P)
    (path : ActualUpdatePath P source target) :
    WriteBackReceipt P source target path where
  value := P.toPathIndexedResidualTransport.pathWriteBack path
  value_eq := rfl
  live_eq := by
    change P.residual target.state = target.value
    exact target.value_eq.symm
  trace_eq := rfl
  recollects_source := by
    rw [P.toPathIndexedResidualTransport.pathWriteBack_recollects_source]
    exact source.value_eq.symm

/-- Authoritative conversion to the shared native lifecycle schema. -/
def Recognition.toNativeResidualUpdateProcess
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P)
    (R : Recognition P) : NativeResidualUpdate.Process where
  Residual := ResidualState P
  Content := R.Content
  Bearer := R.Bearer
  Scope := S.Scope
  Lineage := S.Lineage
  Incidence := S.Incidence
  SourceObservation := S.SourceObservation
  EventAt := fun current => S.EventAt current.state
  ObstructionAt := fun current => R.ObstructionAt current.state
  update := fun {current} _ => residualState P (P.update current.state)
  content := fun current => R.content current.state
  anchor := fun event => S.anchor event.val
  incidence := fun event => S.incidence event.val
  obstructionContent := R.obstructionContent
  obstructionResidual := fun obstruction =>
    residualState P (R.obstructionResidual obstruction)
  admissionBearer := fun current => R.admissionBearer current.state
  nextBearer := fun {current} _ => R.nextBearer current.state
  KeepAt := fun {current} _ => KeepReceipt P current.state
  TraceAt := fun {current} _ => TraceReceipt P current.state
  PathAt := fun {current} _ target => ActualUpdatePath P current target
  WriteBackAt := fun {current} _ path =>
    WriteBackReceipt P current (residualState P (P.update current.state)) path
  RouteAt := fun {current} _ oldBearer nextBearer =>
    R.RouteAt current.state oldBearer nextBearer
  keepReceipt := fun {current} _ => keepReceipt P current.state
  traceReceipt := fun {current} _ => traceReceipt P current.state
  pathReceipt := fun {current} _ => P.updatePath current.state 1
  writeBackReceipt := fun {current} _ =>
    writeBackReceipt P current (residualState P (P.update current.state))
      (P.updatePath current.state 1)
  routeReceipt := fun {current} _ oldBearer =>
    R.routeReceipt current.state oldBearer
  content_update := fun {current} _ => R.content_update current.state

abbrev NativeProcess
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P) :=
  R.toNativeResidualUpdateProcess P S

instance nativeProcessBearerDecidableEq
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer] :
    DecidableEq (NativeProcess P S R).Bearer := by
  change DecidableEq R.Bearer
  infer_instance

abbrev V
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P) :=
  NativeResidualUpdate.V (NativeProcess P S R)

abbrev ResponsibilityProcess
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer] :=
  NativeResidualUpdate.RP (NativeProcess P S R)

/-- Thin recognition of an actual producer obstruction at one effective
state. -/
def Recognition.admissionEvent
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    (emitted : S.Event)
    (obstruction : R.ObstructionAt (S.source emitted))
    (content_eq :
      R.obstructionContent obstruction = R.content (S.source emitted))
    (residual_eq :
      R.obstructionResidual obstruction = S.source emitted) :
    NativeResidualUpdate.AdmissionEvent (NativeProcess P S R) where
  source := ⟨residualState P (S.source emitted), ⟨emitted, rfl⟩⟩
  obstruction := obstruction
  content_eq := content_eq
  residual_eq := congrArg (residualState P) residual_eq

/-- The exact same-source total family as a native lifecycle event producer.
The origin is the emitted event itself, so later prefix steps cannot refresh
their anchor or incidence. -/
def ActualProgressSource.TotalAt.toNativeTotal
    (P : EffectiveResidualProcess K E State)
    {S : ActualProgressSource P} {origin : S.Event}
    (total : S.TotalAt origin) (R : Recognition P) :
    NativeResidualUpdate.Total (NativeProcess P S R)
      (⟨residualState P (S.source origin), ⟨origin, rfl⟩⟩ :
        NativeResidualUpdate.SourceEvent (NativeProcess P S R)) where
  event := fun residual => total.eventAt residual.state
  anchor_eq := fun residual => total.anchor_eq residual.state
  incidence_eq := fun residual => total.incidence_eq residual.state

@[simp] theorem nativeProcess_update_state
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    {state : State} (event : S.EventAt state) :
    ((NativeProcess P S R).update
      (current := residualState P state) event).state = P.update state := by
  rfl

/-- The lifecycle target stores the effective process's transported residual,
not a state label plus an unrelated equality. -/
theorem nativeProcess_update_value_eq_keep
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    {state : State} (event : S.EventAt state) :
    ((NativeProcess P S R).update
      (current := residualState P state) event).value =
      P.keep (P.residual state) := by
  exact P.residual_transport_law state

/-- Whole-carrier conservation inherited by the exact actual lifecycle event.
-/
theorem residual_eq_nativeProcess_update_value_add_forcedTrace
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    {state : State} (event : S.EventAt state) :
    P.residual state =
      ((NativeProcess P S R).update
        (current := residualState P state) event).value +
        linearResidualTrace P.keep (P.residual state) := by
  exact effectiveProcess_residual_eq_next_residual_add_trace P state

/-- Iterating a same-source actual event family is exactly the effective
process's own state iteration with its residual reattached. -/
theorem ActualProgressSource.TotalAt.iterate_residualState
    (P : EffectiveResidualProcess K E State)
    {S : ActualProgressSource P} {origin : S.Event}
    (total : S.TotalAt origin) (R : Recognition P)
    (state : State) (length : Nat) :
    (NativeProcess P S R).iterate (total.toNativeTotal P R)
        (residualState P state) length =
      residualState P (P.pathState state length) := by
  induction length with
  | zero =>
      rfl
  | succ length inductionHypothesis =>
      apply ResidualState.ext
      · change P.update
          (((NativeProcess P S R).iterate (total.toNativeTotal P R)
            (residualState P state) length).state) =
          P.update (P.pathState state length)
        exact congrArg P.update
          (congrArg ResidualState.state inductionHypothesis)
      · change P.residual (P.update
          (((NativeProcess P S R).iterate (total.toNativeTotal P R)
            (residualState P state) length).state)) =
          P.residual (P.update (P.pathState state length))
        exact congrArg (fun current => P.residual (P.update current))
          (congrArg ResidualState.state inductionHypothesis)

/-- Actual lifecycle context recognized at one responsibility source state.
It contains no future target or receipt. -/
abbrev ActualProgressEventAt
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    (source : ResponsibilityState (V P S R)) :=
  NativeResidualUpdate.ProgressEventAt (NativeProcess P S R) source

/-- Canonical responsibility edge `Γ(a)` generated from one exact actual
source event. -/
def canonicalCompile
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (actual : ActualProgressEventAt P S R source) :
    (ResponsibilityProcess P S R).Edge source :=
  NativeResidualUpdate.compileProgressEdge (NativeProcess P S R) actual

/-- The designated shared compiler for one exact source state. -/
def canonicalCompiler
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    (source : ResponsibilityState (V P S R)) :
    CanonicalReceiptAuthority.Compiler
      (ActualProgressEventAt P S R source)
      ((ResponsibilityProcess P S R).Edge source) :=
  ⟨canonicalCompile P S R⟩

/-- A lifecycle progress edge is legal exactly when it is the image of the
shared effective-process compiler. -/
abbrev LegalProgressEdge
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (edge : (ResponsibilityProcess P S R).Edge source) :=
  CanonicalReceiptAuthority.CanonicalReceipt
    (canonicalCompiler P S R source) edge

/-- Forward law: an actual source event generates an authoritative lifecycle
progress edge. -/
def canonicalCompile_isLegal
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (actual : ActualProgressEventAt P S R source) :
    LegalProgressEdge P S R (canonicalCompile P S R actual) :=
  (canonicalCompiler P S R source).compileCanonical actual

/-- Exact image theorem: no raw or merely inhabited receipt lies in legal
progress unless it is `Γ(a)` for an actual source event `a`. -/
theorem legalProgress_iff_mem_canonicalCompile_range
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (edge : (ResponsibilityProcess P S R).Edge source) :
    Nonempty (LegalProgressEdge P S R edge) ↔
      edge ∈ Set.range (canonicalCompile P S R) :=
  CanonicalReceiptAuthority.canonicalReceipt_iff_mem_range
    (canonicalCompiler P S R source) edge

/-- Strong converse for the authoritative generated process itself: every
edge whose lifecycle kind is progress is a compiled actual event, without a
caller-supplied legality wrapper. -/
theorem lifecycleProgress_iff_mem_canonicalCompile_range
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (edge : (ResponsibilityProcess P S R).Edge source) :
    edge.lifecycleEvent.kind.IsProgress ↔
      edge ∈ Set.range (canonicalCompile P S R) := by
  constructor
  · intro progressed
    cases edge with
    | admit event =>
        simp [NativeResponsibilityProcess.Edge.lifecycleEvent,
          LifecycleEvent.kind, LifecycleKind.IsProgress] at progressed
    | cross slot obligation present boundary =>
        exact ⟨
          { slot := slot
            obligation := obligation
            present := present
            boundary := boundary },
          rfl⟩
    | reopen slot archive present event =>
        exact nomatch event
  · rintro ⟨actual, rfl⟩
    exact NativeResidualUpdate.compileProgressEdge_kind
      (NativeProcess P S R) actual

/-- Converse law: legal progress reveals the exact actual event and the
on-the-nose compiler equation. -/
theorem LegalProgressEdge.exists_exactActualEvent
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    {edge : (ResponsibilityProcess P S R).Edge source}
    (legal : LegalProgressEdge P S R edge) :
    ∃ actual : ActualProgressEventAt P S R source,
      canonicalCompile P S R actual = edge :=
  CanonicalReceiptAuthority.CanonicalReceipt.exists_exactActualEvent legal

/-- Every legal edge identifies a nonterminal actual source fibre. -/
theorem LegalProgressEdge.exists_nonterminalActualEvent
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    {edge : (ResponsibilityProcess P S R).Edge source}
    (legal : LegalProgressEdge P S R edge) :
    ∃ actual : ActualProgressEventAt P S R source,
      canonicalCompile P S R actual = edge ∧
        ¬ S.TerminalAt actual.boundary.source.current.state := by
  rcases legal.exists_exactActualEvent P S R with ⟨actual, actual_eq⟩
  exact ⟨actual, actual_eq,
    S.not_terminal_of_event actual.boundary.source.event⟩

@[simp] theorem canonicalCompile_kind
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (actual : ActualProgressEventAt P S R source) :
    (canonicalCompile P S R actual).lifecycleEvent.kind.IsProgress :=
  NativeResidualUpdate.compileProgressEdge_kind (NativeProcess P S R) actual

/-- The compiled lifecycle target is the effective process's exact native
update, not a state inferred from the residual conservation equality. -/
theorem canonicalCompile_target_residual
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (actual : ActualProgressEventAt P S R source) :
    ∃ targetObligation,
      (canonicalCompile P S R actual).target.slots[actual.slot.val]? =
          some (.live targetObligation) ∧
        targetObligation.residual =
          residualState P
            (P.update actual.boundary.source.current.state) := by
  refine ⟨NativeResidualUpdate.nextObligation
    (NativeProcess P S R) actual.boundary, ?_, rfl⟩
  exact NativeResidualUpdate.compileProgressEdge_target_at_slot
    (NativeProcess P S R) actual

/-- Stuttering cannot be compiled as progress.  Unchanged custody must use
the independently debited maintenance lifecycle. -/
theorem canonicalCompile_update_ne_source
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (actual : ActualProgressEventAt P S R source) :
    P.update actual.boundary.source.current.state ≠
      actual.boundary.source.current.state :=
  by
    simpa [actual.boundary.source.event.property] using
      S.update_ne_source actual.boundary.source.event.val

/-- Source Anchor Conservation: canonical progress can only pay an obligation
whose admission source carries the same O0 anchor as the exact actual event. -/
theorem canonicalCompile_sourceAnchor_eq_admissionAnchor
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (actual : ActualProgressEventAt P S R source) :
    actual.boundary.source.anchor =
      actual.obligation.admission.sourceEvent.anchor :=
  actual.boundary.anchor_eq

/-- The event can settle only the exact responsibility incidence named by the
obligation's admission source.  Reusable rules remain legal, but they cannot
be redirected to another incidence by a scalar endpoint match. -/
theorem canonicalCompile_incidence_eq_admissionIncidence
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (actual : ActualProgressEventAt P S R source) :
    actual.boundary.source.incidence =
      actual.obligation.admission.sourceEvent.incidence :=
  actual.boundary.incidence_eq

theorem canonicalCompile_admissionScope_eq_anchorScope
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (actual : ActualProgressEventAt P S R source) :
    actual.obligation.admission.admittedScope =
      actual.boundary.source.scope := by
  change actual.obligation.admission.admittedScope =
    actual.boundary.source.anchor.scope
  exact actual.obligation.admittedScope_eq_sourceAnchorScope.trans
    (congrArg MinimalRegistrableSourceAnchor.scope
      actual.boundary.anchor_eq.symm)

theorem canonicalCompile_lineage_eq_anchorLineage
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (actual : ActualProgressEventAt P S R source) :
    actual.obligation.lineage = actual.boundary.source.lineage := by
  change actual.obligation.lineage = actual.boundary.source.anchor.lineage
  exact actual.obligation.lineage_eq_sourceAnchorLineage.trans
    (congrArg MinimalRegistrableSourceAnchor.lineage
      actual.boundary.anchor_eq.symm)

/-- The canonical progress receipt simultaneously carries the generated keep,
forced trace, typed update path, and write-back of the same actual event. -/
theorem canonicalCompile_disposition
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    {source : ResponsibilityState (V P S R)}
    (actual : ActualProgressEventAt P S R source) :
    (∃ receipt,
        (ResponsibilityProcess P S R).boundaryDisposition actual.boundary =
          .carry (.progressed actual.boundary.source.next receipt)) ∨
      ∃ progressReceipt transferReceipt,
        (ResponsibilityProcess P S R).boundaryDisposition actual.boundary =
          .carry (.progressedAndTransferred actual.boundary.source.next
            actual.boundary.source.nextBearer progressReceipt
            transferReceipt) :=
  NativeResidualUpdate.boundaryDisposition_shape
    (NativeProcess P S R) actual.boundary

/-! ## Same-source finite execution -/

/-- Arbitrary finite exact-target prefix generated from one emitted origin
and its source-owned total event law. The target, path, receipts, and outcome
remain outputs of the effective/native compilers. -/
noncomputable def Recognition.generatedPrefix
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    (origin : S.Event)
    (obstruction : R.ObstructionAt (S.source origin))
    (content_eq :
      R.obstructionContent obstruction = R.content (S.source origin))
    (residual_eq :
      R.obstructionResidual obstruction = S.source origin)
    (total : S.TotalAt origin) (length : Nat) :
    NativeResidualUpdate.GeneratedPrefix
      (NativeProcess P S R)
      (R.admissionEvent P S origin obstruction content_eq residual_eq)
      length :=
  NativeResidualUpdate.generatedPrefix
    (NativeProcess P S R)
    (admission := R.admissionEvent P S origin obstruction content_eq residual_eq)
    (total.toNativeTotal P R) length

theorem Recognition.generatedPrefix_events_length
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    (origin : S.Event)
    (obstruction : R.ObstructionAt (S.source origin))
    (content_eq :
      R.obstructionContent obstruction = R.content (S.source origin))
    (residual_eq :
      R.obstructionResidual obstruction = S.source origin)
    (total : S.TotalAt origin) (length : Nat) :
    (R.generatedPrefix P S origin obstruction content_eq residual_eq total
      length).run.events.length = length :=
  NativeResidualUpdate.generatedPrefix_events_length
    (NativeProcess P S R)
    (admission := R.admissionEvent P S origin obstruction content_eq residual_eq)
    (total.toNativeTotal P R) length

/-- The finite-prefix target is the effective process's literal path state. -/
theorem Recognition.generatedPrefix_target_residual
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    (origin : S.Event)
    (obstruction : R.ObstructionAt (S.source origin))
    (content_eq :
      R.obstructionContent obstruction = R.content (S.source origin))
    (residual_eq :
      R.obstructionResidual obstruction = S.source origin)
    (total : S.TotalAt origin) (length : Nat) :
    (R.generatedPrefix P S origin obstruction content_eq residual_eq total
      length).target.obligation.residual =
      residualState P (P.pathState (S.source origin) length) := by
  exact (NativeResidualUpdate.generatedPrefix_target_residual
      (NativeProcess P S R)
      (admission := R.admissionEvent P S origin obstruction content_eq residual_eq)
      (total.toNativeTotal P R) length).trans
    (total.iterate_residualState P R (S.source origin) length)

/-- The target bearer belongs to the same actual event iteration. -/
theorem Recognition.generatedPrefix_target_bearer
    (P : EffectiveResidualProcess K E State)
    (S : ActualProgressSource P) (R : Recognition P)
    [DecidableEq R.Bearer]
    (origin : S.Event)
    (obstruction : R.ObstructionAt (S.source origin))
    (content_eq :
      R.obstructionContent obstruction = R.content (S.source origin))
    (residual_eq :
      R.obstructionResidual obstruction = S.source origin)
    (total : S.TotalAt origin) (length : Nat) :
    (R.generatedPrefix P S origin obstruction content_eq residual_eq total
      length).target.obligation.bearer =
      (NativeProcess P S R).iterateBearer (total.toNativeTotal P R)
        (residualState P (S.source origin)) length :=
  NativeResidualUpdate.generatedPrefix_target_bearer
    (NativeProcess P S R)
    (admission := R.admissionEvent P S origin obstruction content_eq residual_eq)
    (total.toNativeTotal P R) length

end EffectiveResidualUpdate
end ResponsibilityLifecycle
end SaturationMonoid
