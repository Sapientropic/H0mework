import H0mework.Runtime.Pending.ResidualPath

/-!
# Additive runtime edge trace versus idempotent materialization

A concrete map from consumed-event memory to edge-trace memory can commute
with write-back on the whole carrier:

```text
(pending live, consumed-event memory)
  ↦ (pending live, additive edge-trace memory).
```

The target update adds the mapped complementary pending trace.  Native
`RuntimeGraphState.edges`, however, is a `Finset` updated by idempotent union.
Its linear 0/1 model must overwrite the selected edge coordinate rather than
add to it.  The final theorem gives an explicit whole-carrier counterexample:
the additive write-back square cannot be reinterpreted as that native
overwrite square.

Actual fresh paths may still lie in the locus where additive multiplicity and
0/1 materialization agree.  That pointwise alignment is a concrete regression
fact, not global faithfulness.
-/

noncomputable section

namespace SaturationMonoid
namespace RuntimeGraphResidual

open AffineRelaxation
open ResidualProjection

variable {EventId Key : Type}
variable [DecidableEq EventId] [DecidableEq Key]

/-- Additive multiplicity carried by materialized runtime edges. -/
abbrev RuntimeGraphEdgeTraceResidual (Key : Type) :=
  Key →₀ ℚ

/-- Send each event-memory basis vector to its selected edge basis vector.
Collisions, if any, add multiplicities; no injectivity is assumed. -/
noncomputable def runtimeGraphEventMemoryToEdgeTrace
    (eventEdge : EventId → Key) :
    RuntimeGraphPendingIndicatorResidual EventId →ₗ[ℚ]
      RuntimeGraphEdgeTraceResidual Key :=
  Finsupp.lmapDomain ℚ ℚ eventEdge

omit [DecidableEq EventId] [DecidableEq Key] in
@[simp] theorem runtimeGraphEventMemoryToEdgeTrace_single
    (eventEdge : EventId → Key)
    (eventId : EventId)
    (coefficient : ℚ) :
    runtimeGraphEventMemoryToEdgeTrace eventEdge
        (Finsupp.single eventId coefficient) =
      Finsupp.single (eventEdge eventId) coefficient := by
  simp [
    runtimeGraphEventMemoryToEdgeTrace,
    Finsupp.lmapDomain_apply]

/-- Coordinate deletion generates precisely the selected event basis
coefficient. -/
theorem runtimeGraphPendingEraseTrace_eq_single
    (eventId : EventId)
    (residual : RuntimeGraphPendingIndicatorResidual EventId) :
    linearResidualTrace
        (runtimeGraphPendingEraseKeep eventId) residual =
      Finsupp.single eventId (residual eventId) := by
  ext current
  by_cases selected : current = eventId
  · subst current
    simp [
      linearResidualTrace,
      runtimeGraphPendingEraseKeep]
  · simp [
    linearResidualTrace,
    runtimeGraphPendingEraseKeep,
    selected]

/-- Lift consumed-event write-back to pending-live plus additive edge-trace
memory. -/
noncomputable def runtimeGraphPendingWriteBackToEdgeTrace
    (eventEdge : EventId → Key) :
    ResidualTraceWriteBackCarrier
        (RuntimeGraphPendingIndicatorResidual EventId) →ₗ[ℚ]
      (RuntimeGraphPendingIndicatorResidual EventId ×
        RuntimeGraphEdgeTraceResidual Key) where
  toFun state :=
    (state.1,
      runtimeGraphEventMemoryToEdgeTrace eventEdge state.2)
  map_add' := by
    intro left right
    simp
  map_smul' := by
    intro scalar state
    simp

/-- Whole-carrier target keep for additive edge-trace memory.  It transfers
the selected pending coordinate through the concrete event-to-edge map. -/
noncomputable def runtimeGraphPendingEdgeTraceAdditiveKeep
    (eventEdge : EventId → Key)
    (eventId : EventId) :
    (RuntimeGraphPendingIndicatorResidual EventId ×
        RuntimeGraphEdgeTraceResidual Key) →ₗ[ℚ]
      (RuntimeGraphPendingIndicatorResidual EventId ×
        RuntimeGraphEdgeTraceResidual Key) where
  toFun state :=
    (runtimeGraphPendingEraseKeep eventId state.1,
      state.2 +
        runtimeGraphEventMemoryToEdgeTrace eventEdge
          (linearResidualTrace
            (runtimeGraphPendingEraseKeep eventId) state.1))
  map_add' := by
    intro left right
    apply Prod.ext
    · simp
    · simp [linearResidualTrace]
      abel
  map_smul' := by
    intro scalar state
    apply Prod.ext
    · simp
    · simp [linearResidualTrace, smul_add, smul_sub]

omit [DecidableEq Key] in
/-- Gate 2: the event-memory-to-edge-trace lift commutes with additive
write-back on every live/memory carrier value. -/
theorem runtimeGraphPendingWriteBackToEdgeTrace_keep_commutes
    (eventEdge : EventId → Key)
    (eventId : EventId)
    (state :
      ResidualTraceWriteBackCarrier
        (RuntimeGraphPendingIndicatorResidual EventId)) :
    runtimeGraphPendingWriteBackToEdgeTrace eventEdge
        (residualTraceWriteBackKeep
          (runtimeGraphPendingEraseKeep eventId) state) =
      runtimeGraphPendingEdgeTraceAdditiveKeep eventEdge eventId
        (runtimeGraphPendingWriteBackToEdgeTrace eventEdge state) := by
  apply Prod.ext
  · rfl
  · simp [
      runtimeGraphPendingWriteBackToEdgeTrace,
      runtimeGraphPendingEdgeTraceAdditiveKeep,
      residualTraceWriteBackKeep]

/-! ## Native 0/1 materialization -/

/-- Linear overwrite model for a singleton native edge union.  The old edge
coordinate is erased before the current pending coefficient is installed. -/
def runtimeGraphPendingEdgeSetOverwriteKeep
    (eventEdge : EventId → Key)
    (eventId : EventId) :
    (RuntimeGraphPendingIndicatorResidual EventId ×
        RuntimeGraphEdgeTraceResidual Key) →ₗ[ℚ]
      (RuntimeGraphPendingIndicatorResidual EventId ×
        RuntimeGraphEdgeTraceResidual Key) where
  toFun state :=
    (runtimeGraphPendingEraseKeep eventId state.1,
      state.2.erase (eventEdge eventId) +
        Finsupp.single (eventEdge eventId) (state.1 eventId))
  map_add' := by
    intro left right
    apply Prod.ext
    · simp
    · ext edge
      by_cases selected : edge = eventEdge eventId
      · subst edge
        simp
      · simp [selected]
  map_smul' := by
    intro scalar state
    apply Prod.ext
    · simp
    · ext edge
      by_cases selected : edge = eventEdge eventId
      · subst edge
        simp
      · simp [selected]

/-- On native 0/1 indicators with an actually pending event, overwrite is
exactly pending erase plus singleton edge union. -/
theorem runtimeGraphPendingEdgeSetOverwriteKeep_indicator
    (eventEdge : EventId → Key)
    (eventId : EventId)
    (pending : Finset EventId)
    (edges : Finset Key)
    (active : eventId ∈ pending) :
    runtimeGraphPendingEdgeSetOverwriteKeep eventEdge eventId
        (runtimeGraphPendingIndicator pending,
          runtimeGraphPendingIndicator edges) =
      (runtimeGraphPendingIndicator (pending.erase eventId),
        runtimeGraphPendingIndicator
          (edges ∪ {eventEdge eventId})) := by
  apply Prod.ext
  · exact runtimeGraphPendingEraseKeep_indicator pending eventId
  · ext edge
    by_cases selected : edge = eventEdge eventId
    · subst edge
      simp [
        runtimeGraphPendingEdgeSetOverwriteKeep,
        runtimeGraphPendingIndicator_apply,
        active]
    · simp [
      runtimeGraphPendingEdgeSetOverwriteKeep,
      runtimeGraphPendingIndicator_apply,
      selected]

/-! ## Whole-carrier projection loss -/

/-- Exact alignment locus: additive trace accumulation and native idempotent
overwrite agree on a carrier state exactly when the selected edge has no old
additive multiplicity.  Fresh actual execution images lie in this locus;
arbitrary whole-carrier states do not. -/
theorem
    runtimeGraphPendingEdgeTraceAdditiveKeep_eq_nativeOverwrite_iff
    (eventEdge : EventId → Key)
    (eventId : EventId)
    (state :
      RuntimeGraphPendingIndicatorResidual EventId ×
        RuntimeGraphEdgeTraceResidual Key) :
    runtimeGraphPendingEdgeTraceAdditiveKeep eventEdge eventId state =
        runtimeGraphPendingEdgeSetOverwriteKeep eventEdge eventId state ↔
      state.2 (eventEdge eventId) = 0 := by
  constructor
  · intro keepsEqual
    have selectedCoordinate :=
      congrArg
        (fun output => output.2 (eventEdge eventId))
        keepsEqual
    simp [
      runtimeGraphPendingEdgeTraceAdditiveKeep,
      runtimeGraphPendingEdgeSetOverwriteKeep,
      runtimeGraphPendingEraseTrace_eq_single] at selectedCoordinate
    linarith
  · intro selectedZero
    apply Prod.ext
    · rfl
    · ext current
      by_cases selected : current = eventEdge eventId
      · subst current
        simp [
          runtimeGraphPendingEdgeTraceAdditiveKeep,
          runtimeGraphPendingEdgeSetOverwriteKeep,
          runtimeGraphPendingEraseTrace_eq_single,
          selectedZero]
      · simp [
        runtimeGraphPendingEdgeTraceAdditiveKeep,
        runtimeGraphPendingEdgeSetOverwriteKeep,
        runtimeGraphPendingEraseTrace_eq_single,
        selected]

/-- The additive lift cannot be relabelled as the native idempotent overwrite
square.  Old event memory with zero live responsibility is preserved by
write-back, but native overwrite removes the corresponding selected edge.

This is an exact no-go on the same proposed carrier map, not a claim that
actual fresh execution images fail to align. -/
theorem
    runtimeGraphPendingWriteBackToEdgeTrace_not_commute_nativeOverwrite
    (eventEdge : EventId → Key)
    (eventId : EventId) :
    ¬ ∀ state :
        ResidualTraceWriteBackCarrier
          (RuntimeGraphPendingIndicatorResidual EventId),
      runtimeGraphPendingWriteBackToEdgeTrace eventEdge
          (residualTraceWriteBackKeep
            (runtimeGraphPendingEraseKeep eventId) state) =
        runtimeGraphPendingEdgeSetOverwriteKeep eventEdge eventId
          (runtimeGraphPendingWriteBackToEdgeTrace eventEdge state) := by
  intro commutes
  have contradictionAtSelectedEdge :=
    congrArg
      (fun state =>
        state.2 (eventEdge eventId))
      (commutes
        (0, Finsupp.single eventId 1))
  simp [
    runtimeGraphPendingWriteBackToEdgeTrace,
    runtimeGraphEventMemoryToEdgeTrace,
    runtimeGraphPendingEdgeSetOverwriteKeep,
    residualTraceWriteBackKeep,
    linearResidualTrace,
    runtimeGraphPendingEraseKeep,
    Finsupp.lmapDomain_apply] at contradictionAtSelectedEdge

end RuntimeGraphResidual
end SaturationMonoid
