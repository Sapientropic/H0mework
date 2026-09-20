import H0mework.Realization.Residual.PathTransport
import H0mework.Realization.Observation.LabelJoin

/-!
# Runtime-graph pending-event residual transport

This module gives the generic runtime rewrite of `Proposition19` a native
path-indexed residual carrier.  The audit order is explicit:

1. a typed edge owns one actually pending event and fixes its
   `RuntimeGraph.consumeEvent` target definitionally;
2. the free Dirac carrier on complete runtime states maps linearly to the
   pending-event indicator carrier, and this map commutes with every
   edge-owned keep on the whole carrier;
3. the mapped trace of every actual edge is the unit basis vector at the
   consumed event, so total pending count reads the generated quantum as one.

The generic path transporter then supplies trace cocycles, whole write-back,
and recollection.  The last section also proves a necessary negative result:
for this generic runtime semantics, target pending count below the generated
unit is equivalent to having no outgoing runtime step.  Hence that mouth is a
normal-form readout, not an independent strength-transfer theorem.

No empty target, terminality, observer faithfulness, quantum positivity, or
semantic obstruction is accepted as edge data.
-/

noncomputable section

namespace SaturationMonoid
namespace RuntimeGraphResidual

open ResidualProjection

variable {EventId Key : Type}
variable [DecidableEq EventId] [DecidableEq Key]
variable {A : RuntimeJoinAlgebra}

/-! ## Native typed rewrite quiver -/

/-- A runtime state indexed by its fixed event environment.  The wrapper
distinguishes quivers belonging to different event tables; its only field is
the existing `RuntimeGraphState`. -/
structure RuntimeGraphPendingVertex
    (events : EventId → RuntimeGraphEvent (Key := Key) A) where
  state : RuntimeGraphState (EventId := EventId) (Key := Key) A

/-- A genuine runtime edge.  The caller supplies one event that is actually
pending; the target is the existing `consumeEvent` result, not an arbitrary
state plus a reachability premise. -/
inductive RuntimeGraphPendingEdge
    (events : EventId → RuntimeGraphEvent (Key := Key) A)
    (source : RuntimeGraphPendingVertex events) :
    RuntimeGraphPendingVertex events → Type
  | consume (eventId : EventId)
      (active : eventId ∈ source.state.pending) :
      RuntimeGraphPendingEdge events source
        ⟨RuntimeGraph.consumeEvent events source.state eventId⟩

/-- Named quiver for a fixed runtime event environment. -/
@[reducible] def runtimeGraphPendingQuiver
    (events : EventId → RuntimeGraphEvent (Key := Key) A) :
    Quiver (RuntimeGraphPendingVertex events) where
  Hom := RuntimeGraphPendingEdge events

local instance runtimeGraphPendingQuiverLocal
    (events : EventId → RuntimeGraphEvent (Key := Key) A) :
    Quiver (RuntimeGraphPendingVertex events) :=
  runtimeGraphPendingQuiver events

namespace RuntimeGraphPendingEdge

/-- Event selected by a typed runtime edge. -/
def eventId
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events} :
    RuntimeGraphPendingEdge events source target → EventId
  | .consume eventId _ => eventId

/-- The selected event is pending in the actual edge source. -/
theorem active
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (edge : RuntimeGraphPendingEdge events source target) :
    edge.eventId ∈ source.state.pending := by
  cases edge
  assumption

/-- The target equality is derived from the typed constructor. -/
theorem target_state_eq
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (edge : RuntimeGraphPendingEdge events source target) :
    target.state =
      RuntimeGraph.consumeEvent events source.state edge.eventId := by
  cases edge
  rfl

/-- Forgetting typed provenance recovers the existing runtime relation. -/
theorem toRuntimeStep
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (edge : RuntimeGraphPendingEdge events source target) :
    RuntimeGraph.step events source.state target.state := by
  exact ⟨edge.eventId, edge.active, edge.target_state_eq⟩

/-- Every actual runtime edge removes exactly one pending event. -/
theorem target_card_add_one
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (edge : RuntimeGraphPendingEdge events source target) :
    target.state.pending.card + 1 = source.state.pending.card := by
  rw [edge.target_state_eq]
  change
    (source.state.pending.erase edge.eventId).card + 1 =
      source.state.pending.card
  rw [Finset.card_erase_of_mem edge.active]
  exact
    Nat.sub_add_cancel
      (Finset.card_pos.mpr ⟨edge.eventId, edge.active⟩)

/-- Retain one actual rewrite as a one-edge native path. -/
def toPath
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (edge : source ⟶ target) :
    Quiver.Path source target :=
  .cons .nil edge

end RuntimeGraphPendingEdge

/-! ## Complete-state and pending-indicator carriers -/

/-- Free rational Dirac carrier on complete runtime states. -/
abbrev RuntimeGraphStateDiracResidual
    (events : EventId → RuntimeGraphEvent (Key := Key) A) :=
  RuntimeGraphPendingVertex events →₀ ℚ

/-- Rational pending-event multiplicity carrier. -/
abbrev RuntimeGraphPendingIndicatorResidual (EventId : Type) :=
  EventId →₀ ℚ

/-- Complete runtime vertex represented by its Dirac basis vector. -/
noncomputable def runtimeGraphVertexDirac
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    (vertex : RuntimeGraphPendingVertex events) :
    RuntimeGraphStateDiracResidual events := by
  classical
  exact Finsupp.single vertex 1

/-- Indicator of a finite pending-event set. -/
def runtimeGraphPendingIndicator
    (pending : Finset EventId) :
    RuntimeGraphPendingIndicatorResidual EventId :=
  ∑ eventId ∈ pending, Finsupp.single eventId 1

@[simp] theorem runtimeGraphPendingIndicator_apply
    (pending : Finset EventId) (eventId : EventId) :
    runtimeGraphPendingIndicator pending eventId =
      if eventId ∈ pending then 1 else 0 := by
  classical
  simp [runtimeGraphPendingIndicator, Finsupp.single_apply, eq_comm]

/-! ## Edge-owned keeps -/

/-- Push every complete-state basis vector through consumption of the
edge-selected event. -/
noncomputable def runtimeGraphConsumePushforward
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    (eventId : EventId) :
    RuntimeGraphStateDiracResidual events →ₗ[ℚ]
      RuntimeGraphStateDiracResidual events := by
  classical
  exact
    Finsupp.lmapDomain ℚ ℚ
      (fun vertex =>
        ⟨RuntimeGraph.consumeEvent events vertex.state eventId⟩)

/-- Delete the edge-selected event coordinate on the pending carrier. -/
def runtimeGraphPendingEraseKeep
    (eventId : EventId) :
    RuntimeGraphPendingIndicatorResidual EventId →ₗ[ℚ]
      RuntimeGraphPendingIndicatorResidual EventId where
  toFun residual := residual.erase eventId
  map_add' := by
    intro left right
    ext current
    by_cases same : current = eventId
    · simp [same]
    · simp [same]
  map_smul' := by
    intro scalar residual
    ext current
    by_cases same : current = eventId
    · simp [same]
    · simp [same]

@[simp] theorem runtimeGraphPendingEraseKeep_indicator
    (pending : Finset EventId) (eventId : EventId) :
    runtimeGraphPendingEraseKeep eventId
        (runtimeGraphPendingIndicator pending) =
      runtimeGraphPendingIndicator (pending.erase eventId) := by
  ext current
  simp [runtimeGraphPendingEraseKeep, Finsupp.erase_apply,
    runtimeGraphPendingIndicator_apply]
  by_cases same : current = eventId
  · subst current
    simp
  · simp [same]

/-! ## Gate 1: actual source and pending updates -/

/-- Complete-state Dirac residual transported by the actual edge-owned
push-forward. -/
noncomputable def runtimeGraphStateDiracPathResidualTransport
    (events : EventId → RuntimeGraphEvent (Key := Key) A) :
    PathIndexedResidualTransport ℚ
      (RuntimeGraphStateDiracResidual events)
      (RuntimeGraphPendingVertex events) where
  residual := runtimeGraphVertexDirac
  edgeKeep := fun edge =>
    runtimeGraphConsumePushforward edge.eventId
  edge_residual_transport := by
    intro source target edge
    change RuntimeGraphPendingEdge events source target at edge
    cases edge with
    | consume eventId active =>
        simp [runtimeGraphVertexDirac,
          runtimeGraphConsumePushforward,
          RuntimeGraphPendingEdge.eventId]

/-- Pending indicators transported by actual coordinate deletion. -/
def runtimeGraphPendingIndicatorPathResidualTransport
    (events : EventId → RuntimeGraphEvent (Key := Key) A) :
    PathIndexedResidualTransport ℚ
      (RuntimeGraphPendingIndicatorResidual EventId)
      (RuntimeGraphPendingVertex events) where
  residual := fun vertex =>
    runtimeGraphPendingIndicator vertex.state.pending
  edgeKeep := fun edge =>
    runtimeGraphPendingEraseKeep edge.eventId
  edge_residual_transport := by
    intro source target edge
    change RuntimeGraphPendingEdge events source target at edge
    rw [edge.target_state_eq]
    change
      runtimeGraphPendingIndicator
          (source.state.pending.erase edge.eventId) =
        runtimeGraphPendingEraseKeep edge.eventId
          (runtimeGraphPendingIndicator source.state.pending)
    exact
      (runtimeGraphPendingEraseKeep_indicator
        source.state.pending edge.eventId).symm

/-- Named Gate 1 on the complete-state carrier. -/
theorem runtimeGraphStateDirac_actual_update
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (edge : source ⟶ target) :
    (runtimeGraphStateDiracPathResidualTransport events).residual target =
      (runtimeGraphStateDiracPathResidualTransport events).edgeKeep edge
        ((runtimeGraphStateDiracPathResidualTransport events).residual
          source) :=
  (runtimeGraphStateDiracPathResidualTransport events)
    |>.edge_residual_transport edge

/-- Named Gate 1 on the pending-indicator carrier. -/
theorem runtimeGraphPendingIndicator_actual_update
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (edge : source ⟶ target) :
    (runtimeGraphPendingIndicatorPathResidualTransport events).residual
        target =
      (runtimeGraphPendingIndicatorPathResidualTransport events).edgeKeep
        edge
        ((runtimeGraphPendingIndicatorPathResidualTransport events).residual
          source) :=
  (runtimeGraphPendingIndicatorPathResidualTransport events)
    |>.edge_residual_transport edge

/-! ## Gate 2: whole-carrier pending projection -/

/-- Linearize the pending indicator of every complete-state basis vector. -/
noncomputable def runtimeGraphStateDiracToPendingIndicator
    {events : EventId → RuntimeGraphEvent (Key := Key) A} :
    RuntimeGraphStateDiracResidual events →ₗ[ℚ]
      RuntimeGraphPendingIndicatorResidual EventId :=
  Finsupp.linearCombination ℚ
    (fun vertex =>
      runtimeGraphPendingIndicator vertex.state.pending)

/-- The pending projection commutes with the selected-event update on every
complete-state residual, not only on the actual source Dirac vector. -/
theorem runtimeGraphStateDiracToPendingIndicator_keep_commutes
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    (eventId : EventId)
    (residual : RuntimeGraphStateDiracResidual events) :
    runtimeGraphStateDiracToPendingIndicator
        (events := events)
        (runtimeGraphConsumePushforward
          (events := events) eventId residual) =
      runtimeGraphPendingEraseKeep eventId
        (runtimeGraphStateDiracToPendingIndicator
          (events := events) residual) := by
  have mapEquality :
      (runtimeGraphStateDiracToPendingIndicator
          (events := events)).comp
          (runtimeGraphConsumePushforward
            (events := events) eventId) =
        (runtimeGraphPendingEraseKeep eventId).comp
          (runtimeGraphStateDiracToPendingIndicator
            (events := events)) := by
    apply Finsupp.lhom_ext
    intro vertex coefficient
    simp [runtimeGraphStateDiracToPendingIndicator,
      runtimeGraphConsumePushforward,
      runtimeGraphPendingEraseKeep_indicator,
      RuntimeGraph.consumeEvent]
  exact LinearMap.congr_fun mapEquality residual

/-- Concrete path morphism from complete runtime states to pending-event
indicators.  It carries no faithfulness, quantum, or terminal field. -/
def runtimeGraphStateDiracToPendingIndicatorPathMorphism
    (events : EventId → RuntimeGraphEvent (Key := Key) A) :
    PathIndexedResidualTransport.Morphism
      (runtimeGraphStateDiracPathResidualTransport events)
      (runtimeGraphPendingIndicatorPathResidualTransport events) where
  quiverMap := Prefunctor.id (RuntimeGraphPendingVertex events)
  carrierMap :=
    runtimeGraphStateDiracToPendingIndicator
  residual_naturality := by
    intro vertex
    change
      runtimeGraphStateDiracToPendingIndicator
          (events := events)
          (runtimeGraphVertexDirac vertex) =
        runtimeGraphPendingIndicator vertex.state.pending
    simp [runtimeGraphVertexDirac,
      runtimeGraphStateDiracToPendingIndicator]
  edge_keep_naturality := by
    intro source target edge residual
    exact
      runtimeGraphStateDiracToPendingIndicator_keep_commutes
        edge.eventId residual

/-- Gate 2 path trace naturality. -/
theorem runtimeGraphStateDiracToPendingIndicator_pathTrace_naturality
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (path : Quiver.Path source target) :
    runtimeGraphStateDiracToPendingIndicator
        (events := events)
        ((runtimeGraphStateDiracPathResidualTransport events).pathTrace
          path) =
      (runtimeGraphPendingIndicatorPathResidualTransport events).pathTrace
        ((runtimeGraphStateDiracToPendingIndicatorPathMorphism events)
          |>.mapPath path) :=
  (runtimeGraphStateDiracToPendingIndicatorPathMorphism events)
    |>.pathTrace_naturality path

/-- Gate 2 whole live/memory write-back naturality. -/
theorem runtimeGraphStateDiracToPendingIndicator_pathWriteBack_naturality
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (path : Quiver.Path source target) :
    residualTraceWriteBackMap
        (runtimeGraphStateDiracToPendingIndicator
          (events := events))
        ((runtimeGraphStateDiracPathResidualTransport events).pathWriteBack
          path) =
      (runtimeGraphPendingIndicatorPathResidualTransport events).pathWriteBack
        ((runtimeGraphStateDiracToPendingIndicatorPathMorphism events)
          |>.mapPath path) :=
  (runtimeGraphStateDiracToPendingIndicatorPathMorphism events)
    |>.pathWriteBack_naturality path

/-! ## Gate 3: source-generated unit quantum -/

/-- Total pending-event multiplicity. -/
def runtimeGraphPendingCountObserver :
    RuntimeGraphPendingIndicatorResidual EventId →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ (fun _ => 1)

omit [DecidableEq EventId] in
@[simp] theorem runtimeGraphPendingCountObserver_indicator
    (pending : Finset EventId) :
    runtimeGraphPendingCountObserver
        (runtimeGraphPendingIndicator pending) =
      pending.card := by
  classical
  simp [runtimeGraphPendingCountObserver,
    runtimeGraphPendingIndicator]

/-- The mapped trace of an actual edge is exactly the consumed event's unit
basis vector. -/
theorem runtimeGraphPendingIndicator_edgeTrace_eq_single
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (edge : source ⟶ target) :
    (runtimeGraphPendingIndicatorPathResidualTransport events).pathTrace
        edge.toPath =
      Finsupp.single edge.eventId 1 := by
  rw [
    (runtimeGraphPendingIndicatorPathResidualTransport events)
      |>.pathTrace_eq_source_sub_target edge.toPath]
  ext current
  rw [Finsupp.sub_apply]
  change
    runtimeGraphPendingIndicator source.state.pending current -
        runtimeGraphPendingIndicator target.state.pending current =
      Finsupp.single edge.eventId 1 current
  rw [edge.target_state_eq]
  change
    runtimeGraphPendingIndicator source.state.pending current -
        runtimeGraphPendingIndicator
          (source.state.pending.erase edge.eventId) current =
      Finsupp.single edge.eventId 1 current
  simp only [runtimeGraphPendingIndicator_apply,
    Finsupp.single_apply]
  by_cases same : current = edge.eventId
  · subst current
    simp [edge.active]
  · simp [same, Ne.symm same]

/-- The actual edge trace is read as the unit quantum one. -/
theorem runtimeGraphPendingIndicator_edgeTrace_count_eq_one
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (edge : source ⟶ target) :
    runtimeGraphPendingCountObserver
        ((runtimeGraphPendingIndicatorPathResidualTransport events)
          |>.pathTrace edge.toPath) = 1 := by
  rw [runtimeGraphPendingIndicator_edgeTrace_eq_single]
  simp [runtimeGraphPendingCountObserver]

/-- Gate 3: the generated unit trace avoids the pending-count observer
kernel. -/
theorem runtimeGraphPendingIndicator_edgeTrace_not_mem_countKernel
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (edge : source ⟶ target) :
    (runtimeGraphPendingIndicatorPathResidualTransport events).pathTrace
        edge.toPath ∉
      LinearMap.ker
        (runtimeGraphPendingCountObserver (EventId := EventId)) := by
  rw [LinearMap.mem_ker]
  rw [runtimeGraphPendingIndicator_edgeTrace_count_eq_one]
  norm_num

/-- The generic trace cocycle retained for composable runtime paths. -/
theorem runtimeGraphPendingIndicator_pathTrace_cocycle
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source middle target : RuntimeGraphPendingVertex events}
    (first : Quiver.Path source middle)
    (second : Quiver.Path middle target) :
    (runtimeGraphPendingIndicatorPathResidualTransport events).pathTrace
        (first.comp second) =
      (runtimeGraphPendingIndicatorPathResidualTransport events).pathTrace
          first +
        (runtimeGraphPendingIndicatorPathResidualTransport events).pathTrace
          second :=
  (runtimeGraphPendingIndicatorPathResidualTransport events)
    |>.pathTrace_comp first second

/-- The complete pending write-back recollects the actual path source. -/
theorem runtimeGraphPendingIndicator_pathWriteBack_recollects_source
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (path : Quiver.Path source target) :
    residualTraceWriteBackRecollection (K := ℚ)
        ((runtimeGraphPendingIndicatorPathResidualTransport events)
          |>.pathWriteBack path) =
      (runtimeGraphPendingIndicatorPathResidualTransport events).residual
        source :=
  (runtimeGraphPendingIndicatorPathResidualTransport events)
    |>.pathWriteBack_recollects_source path

/-! ## Target-equivalent normal-form boundary -/

/-- For the generic runtime relation, no outgoing step is exactly emptiness of
the pending-event set. -/
theorem runtimeGraph_noOutgoingStep_iff_pending_eq_empty
    (events : EventId → RuntimeGraphEvent (Key := Key) A)
    (state : RuntimeGraphState (EventId := EventId) (Key := Key) A) :
    (¬ ∃ target, RuntimeGraph.step events state target) ↔
      state.pending = ∅ := by
  constructor
  · intro noStep
    by_contra nonempty
    have pendingNonempty : state.pending.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr nonempty
    rcases pendingNonempty with ⟨eventId, active⟩
    exact
      noStep
        ⟨RuntimeGraph.consumeEvent events state eventId,
          ⟨eventId, active, rfl⟩⟩
  · intro empty
    rintro ⟨target, eventId, active, target_eq⟩
    rw [empty] at active
    simp at active

omit [DecidableEq EventId] in
/-- Pending count below one is itself exactly pending-set emptiness. -/
theorem runtimeGraphPendingCount_abs_lt_one_iff_pending_eq_empty
    (pending : Finset EventId) :
    |runtimeGraphPendingCountObserver
        (runtimeGraphPendingIndicator pending)| < 1 ↔
      pending = ∅ := by
  rw [runtimeGraphPendingCountObserver_indicator]
  constructor
  · intro below
    have nonnegative : (0 : ℚ) ≤ pending.card := by
      positivity
    rw [abs_of_nonneg nonnegative] at below
    have card_lt_one : pending.card < 1 := by
      exact_mod_cast below
    have card_zero : pending.card = 0 := by
      omega
    exact Finset.card_eq_zero.mp card_zero
  · intro empty
    subst pending
    norm_num

/-- Machine no-go: on an actual edge target, residual below the generated
unit quantum is equivalent to the target already having no outgoing runtime
step.  It must therefore not be advertised as an independent semantic or
cross-domain strength transfer. -/
theorem
    runtimeGraphPendingIndicator_targetBelowGeneratedQuantum_iff_noOutgoingStep
    {events : EventId → RuntimeGraphEvent (Key := Key) A}
    {source target : RuntimeGraphPendingVertex events}
    (edge : source ⟶ target) :
    |runtimeGraphPendingCountObserver
        ((runtimeGraphPendingIndicatorPathResidualTransport events).residual
          target)| <
        |runtimeGraphPendingCountObserver
          ((runtimeGraphPendingIndicatorPathResidualTransport events)
            |>.pathTrace edge.toPath)| ↔
      ¬ ∃ next, RuntimeGraph.step events target.state next := by
  rw [runtimeGraphPendingIndicator_edgeTrace_count_eq_one]
  norm_num only [abs_one]
  change
    |runtimeGraphPendingCountObserver
        (runtimeGraphPendingIndicator target.state.pending)| < 1 ↔
      ¬ ∃ next, RuntimeGraph.step events target.state next
  rw [
    runtimeGraphPendingCount_abs_lt_one_iff_pending_eq_empty,
    ← runtimeGraph_noOutgoingStep_iff_pending_eq_empty]

end RuntimeGraphResidual
end SaturationMonoid
