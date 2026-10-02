import H0mework.Realization.Operations.Execution.Debt.Source
import H0mework.Foundation.Ledger.SourceCompiler

/-! One source-owned normalization request retains its original occurrence, raw input and paid past. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource

open SourceOperationEffects

variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}

structure RawInputAt (lower : SourceNativeLedgerRootClosure N V) (current : V.Current)
    (occurrence : lower.source.source.toRootSource.actual.OccurrenceAt current) : Type u where
  environment : Env Value Var
  expression : Expr Value Var sort
  owner : OpenResponsibilityAt N (lower.source.source.toRootSource.account.supportOf occurrence)

structure RegisteredAt (lower : SourceNativeLedgerRootClosure N V) (origin : V.Current) : Type u where
  private mk ::
  input : RawInputAt (Value := Value) (Var := Var) (sort := sort) lower origin (lower.emitted origin)

/-- The exact original occurrence is read before a mathematical event is created. -/
def register {lower : SourceNativeLedgerRootClosure N V} {origin : V.Current}
    (reader : (occurrence : lower.source.source.toRootSource.actual.OccurrenceAt origin) →
      RawInputAt (Value := Value) (Var := Var) (sort := sort) lower origin occurrence) :
    RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin :=
  ⟨reader (lower.emitted origin)⟩

variable {lower : SourceNativeLedgerRootClosure N V} {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin)

abbrev law := SourceOperationExecutionDebt.law registered.input.environment registered.input.expression

/-- The environment and raw expression remain those of the original registration. -/
structure EventAt (current : V.Current) : Type u where
  private mk ::
  state : SourceOperationExecutionDebt.State registered.input.environment registered.input.expression
  owner : OpenResponsibilityAt N
    (lower.source.source.toRootSource.account.supportOf (lower.emitted current))

def initialEvent : EventAt registered origin :=
  ⟨SourceOperationExecutionDebt.initial registered.input.environment registered.input.expression,
    registered.input.owner⟩

variable {registered} {current : V.Current}

def mathAction (event : EventAt registered current) :
    SourceOperationExecutionDebt.Settlement event.state ⊕
      DebtActivationWorld.GeneratedStepAt (law registered) event.state :=
  SourceOperationExecutionDebt.generate registered.input.environment registered.input.expression event.state

def mathTarget (event : EventAt registered current) : (law registered).DebtState :=
  match mathAction event with
  | .inl _ => event.state
  | .inr paid => paid.1

private theorem successor_target_emitted
    {source : SourceNativeSource N V}
    (emitted : (current : V.Current) → source.toRootSource.actual.OccurrenceAt current)
    {current : V.Current} {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt source occurrence}
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated)
    (commutes : generated.CommutesWith emitted) :
    successor.targetOccurrence = emitted successor.targetCurrent := by
  cases generated with
  | nativeWrite => exact commutes
  | relationWrite => exact commutes
  | continuedTransport => exact commutes
  | borromeanRedirect => exact commutes
  | faithfulTerminal => exact nomatch successor

/-- The original compiler's generated successor determines the next owner;
the same registered mathematical action determines its paid state. -/
def successorEvent (event : EventAt registered current)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (lower.emitted current)
      (lower.generatedLedgerAt current)) :
    EventAt registered successor.targetCurrent :=
  ⟨mathTarget event,
    successor_target_emitted lower.emitted successor (lower.compiler_commutes current) ▸
      (successor.ledgerEvolution.destination event.owner).1⟩

@[simp] theorem successorEvent_state (event : EventAt registered current)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (lower.emitted current)
      (lower.generatedLedgerAt current)) :
    (successorEvent event successor).state = mathTarget event := rfl

theorem successorEvent_owner (event : EventAt registered current)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (lower.emitted current)
      (lower.generatedLedgerAt current)) :
    HEq (successorEvent event successor).owner
      (successor.ledgerEvolution.destination event.owner).1 := by
  unfold successorEvent
  exact eqRec_heq_iff.mpr HEq.rfl

/-- A native result is introduced only by eliminating the original compiler's native-write image. -/
structure NativeAt (event : EventAt registered current) : Type u where
  private mk ::
  write : V.NativeWriteAt current
  structural_eq : lower.source.source.toRootSource.actual.compile (lower.emitted current) = .nativeWrite write
  targetOccurrence : lower.source.source.toRootSource.actual.OccurrenceAt (V.nativeTarget write)
  target_emitted : targetOccurrence = lower.emitted (V.nativeTarget write)
  baseLedger : LedgerWriteEvolutionAt N
    ⟨lower.source.source.toRootSource.account.supportOf (lower.emitted current)⟩
    ⟨lower.source.source.toRootSource.account.supportOf targetOccurrence⟩
  nextEvent : EventAt registered (V.nativeTarget write)
  next_state : nextEvent.state = mathTarget event

/-- An already generated native image supplies the old update and ledger.
The source computes the next owner and mathematical event from that receipt. -/
def nativeFromGenerated (event : EventAt registered current)
    (write : V.NativeWriteAt current)
    (structuralEq : lower.source.source.toRootSource.actual.compile (lower.emitted current) = .nativeWrite write)
    (targetOccurrence : lower.source.source.toRootSource.actual.OccurrenceAt (V.nativeTarget write))
    (baseLedger : LedgerWriteEvolutionAt N
      ⟨lower.source.source.toRootSource.account.supportOf (lower.emitted current)⟩
      ⟨lower.source.source.toRootSource.account.supportOf targetOccurrence⟩)
    (generatedEq : lower.generatedLedgerAt current = .nativeWrite write structuralEq targetOccurrence baseLedger) :
    NativeAt event := by
  have targetEmitted : targetOccurrence = lower.emitted (V.nativeTarget write) := by
    have commutes := lower.compiler_commutes current
    change (lower.generatedLedgerAt current).CommutesWith lower.emitted at commutes
    rw [generatedEq] at commutes
    exact commutes
  let nextOwner : OpenResponsibilityAt N
      (lower.source.source.toRootSource.account.supportOf (lower.emitted (V.nativeTarget write))) :=
    targetEmitted ▸ (baseLedger.destination event.owner).1
  let nextEvent : EventAt registered (V.nativeTarget write) := ⟨mathTarget event, nextOwner⟩
  exact ⟨write, structuralEq, targetOccurrence, targetEmitted, baseLedger, nextEvent, rfl⟩

/-- Other original structural branches stay outside this native feed; no new root is installed. -/
def compileNative? (event : EventAt registered current) : Option (NativeAt event) := by
  cases generatedEq : lower.generatedLedgerAt current with
  | nativeWrite write structuralEq targetOccurrence baseLedger =>
      exact some (nativeFromGenerated event write structuralEq targetOccurrence baseLedger generatedEq)
  | relationWrite _ _ _ _ => exact none
  | continuedTransport _ _ _ _ => exact none
  | borromeanRedirect _ _ _ _ => exact none
  | faithfulTerminal _ _ _ => exact none

theorem local_completed_value (event : EventAt registered current)
    (settled : SourceOperationExecutionDebt.Settlement event.state) :
    settled.1 = registered.input.expression.eval registered.input.environment :=
  SourceOperationExecutionDebt.completed_value event.state settled

end RootGeneratedDebtActivationJointSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
