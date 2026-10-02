import H0mework.Foundation.Responsibility.JointSource.Native.Ledger
import Mathlib.Data.Fin.Basic

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native

open SourceOperationEffects DebtActivationWorld DebtActivationLedger

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {lower : SourceNativeLedgerRootClosure N V} {origin : V.Current}
variable (program : Program lower)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin)

def mathSource (current : Current registered) :
    OpenResponsibilityAt (World registered) (supportAt registered current) :=
  debtEntry (N := N) (law := Idle.law registered.input.environment registered.input.expression)
    (lower.source.source.toRootSource.account.supportOf (lower.emitted current.1)) current.2.state

def mathTargetEntry (current : Current registered) :
    OpenResponsibilityAt (World registered) (supportAt registered (targetCurrent program registered current)) :=
  debtEntry (N := N) (law := Idle.law registered.input.environment registered.input.expression)
    (lower.source.source.toRootSource.account.supportOf (lower.emitted (targetCurrent program registered current).1))
    (targetCurrent program registered current).2.state

def mathRowEvolution (current : Current registered) :
    LedgerEntryEvolutionAt (World registered) (mathSource registered current)
      (mathTargetEntry program registered current) := by
  let generated := native program registered current
  change LedgerEntryEvolutionAt _ _ (debtEntry (law := Idle.law registered.input.environment registered.input.expression)
    (lower.source.source.toRootSource.account.supportOf (lower.emitted (V.nativeTarget generated.write))) generated.nextEvent.state)
  rw [generated.next_state, ← generated.target_emitted]
  unfold mathTarget
  cases mathAction current.2 with
  | inl settled =>
      exact .transferred (debtTransportReceipt _ (Idle.identityTransport current.2.state settled))
        (generated.baseLedger.destination current.2.owner).2.toDebtLineage.lineage_eq rfl
        (Nat.le_refl _)
  | inr paid =>
      exact .transferred (debtStepReceipt (law := Idle.law registered.input.environment registered.input.expression) _ paid.2)
        (generated.baseLedger.destination current.2.owner).2.toDebtLineage.lineage_eq rfl
        (Nat.le_of_lt ((Idle.law registered.input.environment registered.input.expression).step_budget_lt paid.2))

def sourceRow (current : Current registered) :
    Fin ((oldRows program registered current).size + 1) →
      OpenResponsibilityAt (World registered) (supportAt registered current) :=
  Fin.lastCases (motive := fun _ => OpenResponsibilityAt (World registered) (supportAt registered current))
    (mathSource registered current) (fun index =>
    oldEntry (law := Idle.law registered.input.environment registered.input.expression)
      (state? := some current.2.state) ((oldRows program registered current).sourceEntryAt index))

def targetRow (current : Current registered) :
    Fin ((oldRows program registered current).size + 1) →
      OpenResponsibilityAt (World registered) (supportAt registered (targetCurrent program registered current)) :=
  Fin.lastCases (motive := fun _ => OpenResponsibilityAt (World registered)
      (supportAt registered (targetCurrent program registered current)))
    (mathTargetEntry program registered current) (fun index =>
    oldEntry (law := Idle.law registered.input.environment registered.input.expression)
      (state? := some (targetCurrent program registered current).2.state)
      ((oldRows program registered current).targetEntryAt index))

def rowEvolution (current : Current registered) (index : Fin ((oldRows program registered current).size + 1)) :
    LedgerEntryEvolutionAt (World registered) (sourceRow program registered current index)
      (targetRow program registered current index) := by
  refine Fin.lastCases (motive := fun i => LedgerEntryEvolutionAt (World registered)
    (sourceRow program registered current i) (targetRow program registered current i)) ?_ ?_ index
  · simpa only [sourceRow, targetRow, Fin.lastCases_last] using mathRowEvolution program registered current
  · intro old
    simpa only [sourceRow, targetRow, Fin.lastCases_castSucc] using oldRowEvolution program registered current old

inductive RawRowAt :
    {current : Current registered} →
    (occurrence : (source program registered).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (World registered).Support} →
    OpenResponsibilityAt (World registered) ((source program registered).toRootSource.account.supportOf occurrence) →
    OpenResponsibilityAt (World registered) targetSupport → Type u
  | inventory (current : Current registered) (index : Fin ((oldRows program registered current).size + 1)) :
      RawRowAt (emitted program registered current)
        (sourceRow program registered current index) (targetRow program registered current index)

def rowSource : LedgerWriteRowSourceAt (source program registered) (RawRowAt program registered) where
  IncidenceOccurrenceAt := RawRowAt program registered
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    cases event with
    | inventory index => exact rowEvolution program registered current index
  compileExact := fun event => event

def rows (current : Current registered) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource program registered) (emitted program registered current)
      ⟨supportAt registered (targetCurrent program registered current)⟩ where
  size := (oldRows program registered current).size + 1
  sourceEntryAt := sourceRow program registered current
  targetEntryAt := targetRow program registered current
  rowAt index := (rowSource program registered).generate (.inventory current index)

def coverage (current : Current registered) : LedgerCompleteFiniteCoverageAt (rows program registered current) where
  destinationIndex := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl old => exact ((oldCoverage program registered current).destinationIndex ⟨old, opened⟩).castSucc
    | inr _ => exact Fin.last _
  originIndex := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl old => exact ((oldCoverage program registered current).originIndex ⟨old, opened⟩).castSucc
    | inr _ => exact Fin.last _
  destination_sound := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl old =>
        change sourceRow program registered current _ = _
        change sourceRow program registered current
          ((oldCoverage program registered current).destinationIndex ⟨old, opened⟩).castSucc = _
        exact (Fin.lastCases_castSucc
          (motive := fun _ => OpenResponsibilityAt (World registered) (supportAt registered current))
          (last := mathSource registered current)
          (cast := fun index => oldEntry (law := Idle.law registered.input.environment registered.input.expression)
            (state? := some current.2.state) ((oldRows program registered current).sourceEntryAt index))
          ((oldCoverage program registered current).destinationIndex ⟨old, opened⟩)).trans
          (congrArg (oldEntry (law := Idle.law registered.input.environment registered.input.expression)
            (state? := some current.2.state)) ((oldCoverage program registered current).destination_sound ⟨old, opened⟩))
    | inr debtId =>
        rcases opened with ⟨⟨same⟩⟩
        subst debtId
        change sourceRow program registered current (Fin.last _) = _
        simp only [sourceRow, Fin.lastCases_last]
        rfl
  origin_sound := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl old =>
        change targetRow program registered current _ = _
        change targetRow program registered current
          ((oldCoverage program registered current).originIndex ⟨old, opened⟩).castSucc = _
        exact (Fin.lastCases_castSucc
          (motive := fun _ => OpenResponsibilityAt (World registered)
            (supportAt registered (targetCurrent program registered current)))
          (last := mathTargetEntry program registered current)
          (cast := fun index => oldEntry (law := Idle.law registered.input.environment registered.input.expression)
            (state? := some (targetCurrent program registered current).2.state)
            ((oldRows program registered current).targetEntryAt index))
          ((oldCoverage program registered current).originIndex ⟨old, opened⟩)).trans
          (congrArg (oldEntry (law := Idle.law registered.input.environment registered.input.expression)
            (state? := some (targetCurrent program registered current).2.state))
            ((oldCoverage program registered current).origin_sound ⟨old, opened⟩))
    | inr debtId =>
        rcases opened with ⟨⟨same⟩⟩
        subst debtId
        change targetRow program registered current (Fin.last _) = _
        simp only [targetRow, Fin.lastCases_last]
        rfl

def patch (current : Current registered) :
    FiniteGeneratedLedgerWritePatchAt (rowSource program registered) (emitted program registered current)
      ⟨supportAt registered (targetCurrent program registered current)⟩ :=
  .complete (rows program registered current) (coverage program registered current)

end RootGeneratedDebtActivationJointSource.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
