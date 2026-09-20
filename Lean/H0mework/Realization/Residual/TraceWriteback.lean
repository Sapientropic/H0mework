import H0mework.Realization.Residual.Process
import H0mework.Realization.Residual.Morphism

/-!
# Path-indexed residual trace cocycle and write-back

This module derives all history from an existing `EffectiveResidualProcess`.
No path trace, write-back memory, or faithfulness field is supplied by a
caller.
-/

noncomputable section

namespace SaturationMonoid
namespace ResidualProjection

open AffineRelaxation

universe u v w

/-- State reached after a finite path of actual process updates. -/
def EffectiveResidualProcess.pathState
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) : Nat → State
  | 0 => source
  | steps + 1 => P.update (P.pathState source steps)

@[simp] theorem EffectiveResidualProcess.pathState_zero
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) :
    P.pathState source 0 = source := by
  rfl

@[simp] theorem EffectiveResidualProcess.pathState_succ
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) :
    P.pathState source (steps + 1) =
      P.update (P.pathState source steps) := by
  rfl

theorem EffectiveResidualProcess.pathState_add
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (first second : Nat) :
    P.pathState source (first + second) =
      P.pathState (P.pathState source first) second := by
  induction second with
  | zero =>
      simp
  | succ second inductionHypothesis =>
      rw [Nat.add_succ]
      simp only [P.pathState_succ, inductionHypothesis]

/-- Complement accumulated along an actual finite update path. -/
def EffectiveResidualProcess.pathTrace
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) : E :=
  P.residual source - P.residual (P.pathState source steps)

@[simp] theorem EffectiveResidualProcess.pathTrace_zero
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) :
    P.pathTrace source 0 = 0 := by
  simp [EffectiveResidualProcess.pathTrace]

theorem EffectiveResidualProcess.pathTrace_one
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) :
    P.pathTrace source 1 =
      linearResidualTrace P.keep (P.residual source) := by
  simp [EffectiveResidualProcess.pathTrace, linearResidualTrace,
    P.residual_transport_law]

/-- The path trace is the unique complement of the actual endpoint residual. -/
theorem EffectiveResidualProcess.pathTrace_split
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) :
    P.residual source =
      P.residual (P.pathState source steps) +
        P.pathTrace source steps := by
  simp [EffectiveResidualProcess.pathTrace]

theorem EffectiveResidualProcess.pathTrace_unique
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) (trace : E) :
    P.residual source =
        P.residual (P.pathState source steps) + trace ↔
      trace = P.pathTrace source steps := by
  constructor
  · intro split
    rw [EffectiveResidualProcess.pathTrace, split]
    abel
  · intro traceEquation
    rw [traceEquation]
    exact P.pathTrace_split source steps

/-- Additive cocycle law over concatenated actual update paths. -/
theorem EffectiveResidualProcess.pathTrace_add
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (first second : Nat) :
    P.pathTrace source (first + second) =
      P.pathTrace source first +
        P.pathTrace (P.pathState source first) second := by
  rw [EffectiveResidualProcess.pathTrace,
    EffectiveResidualProcess.pathTrace,
    EffectiveResidualProcess.pathTrace,
    P.pathState_add]
  abel

theorem EffectiveResidualProcess.pathTrace_succ
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) :
    P.pathTrace source (steps + 1) =
      P.pathTrace source steps +
        linearResidualTrace P.keep
          (P.residual (P.pathState source steps)) := by
  rw [P.pathTrace_add source steps 1, P.pathTrace_one]

/-! ## Write-back carrier -/

/-- Live residual paired with the uniquely accumulated completed trace. -/
abbrev ResidualTraceWriteBackCarrier (E : Type*) := E × E

/-- Apply an already constructed residual morphism to both the live and
written-back components.  This is the canonical second-order lift; it does
not add a new faithfulness field. -/
def residualTraceWriteBackMap
    {K Source Target : Type*}
    [Field K]
    [AddCommGroup Source] [Module K Source]
    [AddCommGroup Target] [Module K Target]
    (F : Source →ₗ[K] Target) :
    ResidualTraceWriteBackCarrier Source →ₗ[K]
      ResidualTraceWriteBackCarrier Target where
  toFun state := (F state.1, F state.2)
  map_add' := by
    intro left right
    simp
  map_smul' := by
    intro scalar state
    simp

/-- Observe the remaining live residual of a write-back carrier. -/
def residualTraceWriteBackLiveProjection
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] :
    ResidualTraceWriteBackCarrier E →ₗ[K] E where
  toFun state := state.1
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar state
    rfl

/-- Observe the completed trace memory of a write-back carrier. -/
def residualTraceWriteBackMemoryProjection
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] :
    ResidualTraceWriteBackCarrier E →ₗ[K] E where
  toFun state := state.2
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar state
    rfl

@[simp] theorem residualTraceWriteBackMap_apply
    {K Source Target : Type*}
    [Field K]
    [AddCommGroup Source] [Module K Source]
    [AddCommGroup Target] [Module K Target]
    (F : Source →ₗ[K] Target)
    (state : ResidualTraceWriteBackCarrier Source) :
    residualTraceWriteBackMap F state =
      (F state.1, F state.2) := by
  rfl

@[simp] theorem residualTraceWriteBackLiveProjection_apply
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (state : ResidualTraceWriteBackCarrier E) :
    residualTraceWriteBackLiveProjection (K := K) state = state.1 := by
  rfl

@[simp] theorem residualTraceWriteBackMemoryProjection_apply
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (state : ResidualTraceWriteBackCarrier E) :
    residualTraceWriteBackMemoryProjection (K := K) state = state.2 := by
  rfl

/-- Move the current forced trace from the live residual into memory. -/
def residualTraceWriteBackKeep
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) :
    ResidualTraceWriteBackCarrier E →ₗ[K]
      ResidualTraceWriteBackCarrier E where
  toFun state :=
    (keep state.1,
      state.2 + linearResidualTrace keep state.1)
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

/-- A concrete residual morphism commuting with the two keeps automatically
commutes with their whole write-back updates. -/
theorem residualTraceWriteBackMap_keep_commutes
    {K Source Target : Type*}
    [Field K]
    [AddCommGroup Source] [Module K Source]
    [AddCommGroup Target] [Module K Target]
    (F : Source →ₗ[K] Target)
    (sourceKeep : Source →ₗ[K] Source)
    (targetKeep : Target →ₗ[K] Target)
    (keepCommutes :
      ∀ residual,
        F (sourceKeep residual) = targetKeep (F residual))
    (state : ResidualTraceWriteBackCarrier Source) :
    residualTraceWriteBackMap F
        (residualTraceWriteBackKeep sourceKeep state) =
      residualTraceWriteBackKeep targetKeep
        (residualTraceWriteBackMap F state) := by
  apply Prod.ext
  · exact keepCommutes state.1
  · simp [residualTraceWriteBackMap,
      residualTraceWriteBackKeep, linearResidualTrace,
      keepCommutes]

/-- The whole-carrier trace square is forced by the write-back keep square;
it is not an additional transport premise. -/
theorem residualTraceWriteBackMap_keep_and_trace
    {K Source Target : Type*}
    [Field K]
    [AddCommGroup Source] [Module K Source]
    [AddCommGroup Target] [Module K Target]
    (F : Source →ₗ[K] Target)
    (sourceKeep : Source →ₗ[K] Source)
    (targetKeep : Target →ₗ[K] Target)
    (keepCommutes :
      ∀ residual,
        F (sourceKeep residual) = targetKeep (F residual))
    (state : ResidualTraceWriteBackCarrier Source) :
    residualTraceWriteBackMap F
          (residualTraceWriteBackKeep sourceKeep state) =
        residualTraceWriteBackKeep targetKeep
          (residualTraceWriteBackMap F state) ∧
      residualTraceWriteBackMap F
          (linearResidualTrace
            (residualTraceWriteBackKeep sourceKeep) state) =
        linearResidualTrace
          (residualTraceWriteBackKeep targetKeep)
          (residualTraceWriteBackMap F state) := by
  exact
    residualTransportMorphism_keep_and_trace
      (residualTraceWriteBackMap F).toAddMonoidHom
      (residualTraceWriteBackKeep sourceKeep)
      (residualTraceWriteBackKeep targetKeep)
      (residualTraceWriteBackMap_keep_commutes
        F sourceKeep targetKeep keepCommutes)
      state

/-- Actual remaining residual and its completed path trace after `steps`. -/
def EffectiveResidualProcess.pathWriteBackState
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) :
    ResidualTraceWriteBackCarrier E :=
  (P.residual (P.pathState source steps),
    P.pathTrace source steps)

@[simp] theorem EffectiveResidualProcess.pathWriteBackState_zero
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) :
    P.pathWriteBackState source 0 =
      (P.residual source, 0) := by
  simp [EffectiveResidualProcess.pathWriteBackState]

/-- The actual process update transfers precisely its forced trace into the
second carrier component. -/
theorem EffectiveResidualProcess.pathWriteBackState_succ
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) :
    P.pathWriteBackState source (steps + 1) =
      residualTraceWriteBackKeep P.keep
        (P.pathWriteBackState source steps) := by
  apply Prod.ext
  · simp [EffectiveResidualProcess.pathWriteBackState,
      residualTraceWriteBackKeep, P.residual_transport_law]
  · simp [EffectiveResidualProcess.pathWriteBackState,
      residualTraceWriteBackKeep, P.pathTrace_succ]

/-- The path-indexed write-back itself is an effective residual process. -/
def EffectiveResidualProcess.pathWriteBackProcess
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) :
    EffectiveResidualProcess K
      (ResidualTraceWriteBackCarrier E) Nat where
  target := (P.target, 0)
  keep := residualTraceWriteBackKeep P.keep
  residual := P.pathWriteBackState source
  update := Nat.succ
  residual_transport_law := by
    intro steps
    simpa [Nat.succ_eq_add_one] using
      P.pathWriteBackState_succ source steps

/-- Recollect the old residual from live keep plus written-back trace. -/
def residualTraceWriteBackRecollection
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] :
    ResidualTraceWriteBackCarrier E →ₗ[K] E where
  toFun state := state.1 + state.2
  map_add' := by
    intro left right
    simp
    abel
  map_smul' := by
    intro scalar state
    simp [smul_add]

/-- Write-back preserves the recollectable total on the whole carrier. -/
theorem residualTraceWriteBackRecollection_keep
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E)
    (state : ResidualTraceWriteBackCarrier E) :
    residualTraceWriteBackRecollection (K := K)
        (residualTraceWriteBackKeep keep state) =
      residualTraceWriteBackRecollection (K := K) state := by
  simp [residualTraceWriteBackRecollection,
    residualTraceWriteBackKeep, linearResidualTrace]
  abel

/-- The current live residual plus written-back memory reconstructs the
source residual exactly. -/
theorem EffectiveResidualProcess.pathWriteBack_recollects_source
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) :
    residualTraceWriteBackRecollection (K := K)
        (P.pathWriteBackState source steps) =
      P.residual source := by
  simp [residualTraceWriteBackRecollection,
    EffectiveResidualProcess.pathWriteBackState,
    EffectiveResidualProcess.pathTrace]

/-- Conservation forces the memory component; it is not an independent log. -/
theorem EffectiveResidualProcess.pathWriteBack_memory_unique
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) (memory : E) :
    P.residual source =
        P.residual (P.pathState source steps) + memory ↔
      memory = (P.pathWriteBackState source steps).2 := by
  exact P.pathTrace_unique source steps memory

/-- The write-back keep's own complementary trace is an internal transfer:
positive on the live component and negative on the memory component. -/
theorem residualTraceWriteBackKeep_trace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E)
    (state : ResidualTraceWriteBackCarrier E) :
    linearResidualTrace (residualTraceWriteBackKeep keep) state =
      (linearResidualTrace keep state.1,
        -linearResidualTrace keep state.1) := by
  apply Prod.ext
  · simp [linearResidualTrace, residualTraceWriteBackKeep]
  · simp [linearResidualTrace, residualTraceWriteBackKeep]

/-- Total recollection sends the internal transfer trace to zero; this is
conservation, not disappearance of either component. -/
theorem residualTraceWriteBackRecollection_trace_zero
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E)
    (state : ResidualTraceWriteBackCarrier E) :
    residualTraceWriteBackRecollection (K := K)
        (linearResidualTrace
          (residualTraceWriteBackKeep keep) state) = 0 := by
  rw [residualTraceWriteBackKeep_trace]
  simp [residualTraceWriteBackRecollection]

end ResidualProjection
end SaturationMonoid
