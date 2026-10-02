import H0mework.Foundation.Responsibility.JointSource.Native.Source

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

private def consumePayment {current : V.Current} {event : EventAt registered current}
    (generated : NativeAt event) :
    LedgerWriteEvolutionAt (World registered)
      (activeLedger (lower.source.source.toRootSource.account.supportOf (lower.emitted current)) event.state)
      (activeLedger (lower.source.source.toRootSource.account.supportOf generated.targetOccurrence) (mathTarget event)) := by
  cases mathEq : mathAction event with
  | inl settled =>
      have paid := payment generated
      simp only [PaymentAt, mathEq] at paid
      simpa only [mathTarget, mathEq] using paid.1
  | inr actual =>
      have paid := payment generated
      simp only [PaymentAt, mathEq] at paid
      simpa only [mathTarget, mathEq] using paid

private def atTarget {W : WorldRelationNetwork.{u}} {initial target actual : W.Support}
    (same : target = actual) (rows : LedgerWriteEvolutionAt W ⟨initial⟩ ⟨target⟩) :
    LedgerWriteEvolutionAt W ⟨initial⟩ ⟨actual⟩ := same ▸ rows

def wholeEvolution (current : Current registered) :
    LedgerWriteEvolutionAt (World registered) ⟨supportAt registered current⟩
      ⟨supportAt registered (targetCurrent program registered current)⟩ := by
  let generated := native program registered current
  have targetEq :
      (lower.source.source.toRootSource.account.supportOf generated.targetOccurrence,
        some (mathTarget current.2)) = supportAt registered (targetCurrent program registered current) :=
    Prod.ext (congrArg (lower.source.source.toRootSource.account.supportOf)
      generated.target_emitted) (congrArg some generated.next_state.symm)
  exact atTarget targetEq (consumePayment registered generated)

theorem native_write (current : Current registered) :
    (program.emit current.1).write = (native program registered current).write := by
  have same := (program.emit current.1).structural_eq.symm.trans
    (native program registered current).structural_eq
  exact EvolutionAt.nativeWrite.inj same

theorem image_target (current : Current registered) :
    (program.emit current.1).targetOccurrence =
      lower.emitted (targetCurrent program registered current).1 :=
  (program.emit current.1).target_emitted


/-- Rows and selectors are transported together; no index is discarded. -/
def oldPacket (current : Current registered) :
    Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
      (lower.emitted current.1)
      ⟨lower.source.source.toRootSource.account.supportOf (lower.emitted (targetCurrent program registered current).1)⟩,
      LedgerCompleteFiniteCoverageAt rows :=
  image_target program registered current ▸
    ⟨(program.emit current.1).rows, (program.emit current.1).coverage⟩

def oldRows (current : Current registered) := (oldPacket program registered current).1

def oldCoverage (current : Current registered) := (oldPacket program registered current).2

private theorem castPacket_size {target actual : lower.source.source.toRootSource.actual.OccurrenceAt
    (V.nativeTarget (program.emit (origin)).write)}
    (same : target = actual)
    (packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
      (lower.emitted origin) ⟨lower.source.source.toRootSource.account.supportOf target⟩,
      LedgerCompleteFiniteCoverageAt rows) :
    ((same ▸ packet : Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
      (lower.emitted origin) ⟨lower.source.source.toRootSource.account.supportOf actual⟩,
      LedgerCompleteFiniteCoverageAt rows).1).size = packet.1.size := by
  cases same
  rfl

theorem oldRows_size (current : Current registered) :
    (oldRows program registered current).size = (program.emit current.1).rows.size := by
  unfold oldRows oldPacket
  exact castPacket_size (origin := current.1) program (image_target program registered current)
    ⟨(program.emit current.1).rows, (program.emit current.1).coverage⟩

def oldRowEvolution (current : Current registered) (index : Fin (oldRows program registered current).size) :
    LedgerEntryEvolutionAt (World registered)
      (oldEntry (law := Idle.law registered.input.environment registered.input.expression)
        (state? := some current.2.state) ((oldRows program registered current).sourceEntryAt index))
      (oldEntry (law := Idle.law registered.input.environment registered.input.expression)
        (state? := some (targetCurrent program registered current).2.state)
        ((oldRows program registered current).targetEntryAt index)) := by
  change LedgerEntryEvolutionAt _ _ (oldEntry
    (law := Idle.law registered.input.environment registered.input.expression)
    (state? := some (native program registered current).nextEvent.state) _)
  rw [(native program registered current).next_state]
  unfold mathTarget
  cases mathAction current.2 with
  | inl settled =>
      exact RootGeneratedDebtActivationU7.mapOldEntryEvolution
        (law := Idle.law registered.input.environment registered.input.expression)
        (state? := some current.2.state) ((oldRows program registered current).rowAt index).evolution
  | inr paid =>
      exact jointOldEvolution (law := Idle.law registered.input.environment registered.input.expression) paid.2 ((oldRows program registered current).rowAt index).evolution

end RootGeneratedDebtActivationJointSource.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
