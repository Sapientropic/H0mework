import H0mework.Versions.Y.Arithmetic.PrimeShadow.DomainConsumers.CanonicalArithmetic.Relation.NativeReceiptBlockProjectionConsumer
import H0mework.Versions.Y.Arithmetic.PrimeShadow.DomainConsumers.CanonicalArithmetic.Relation.NativeReceiptBlockBoundaryPersistence

/-!
# The installed block face persists through every original unit successor

The source projection reads the original receipt at each nonempty current.
Its old block consumer stays nonzero, while the coface preserves the original
whole ledger, transfer-row disposition and literal next at every visit.
-/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CanonicalUnitBlockProjectionCoface
open ArithmeticGeneration
open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead
open CanonicalUnitNativeReceiptBlockBoundaryPersistence

noncomputable section

theorem all_later_readout_is_source (stage : Nat) :
    HEq (facade.readoutAt (runtimeAtCoface stage) (.component PUnit.unit))
      (blockComponent.outcomeAt PUnit.unit
        (emitted (runtimeAt stage).current.visit.current)) := by
  change HEq (blockComponent.outcomeAt PUnit.unit
    (emitted (runtimeAtCoface stage).current.visit.current)) _
  rw [same_current stage]

theorem receiptFromGenerated_coface_runtime (stage : Nat) :
    receiptFromGenerated
      (runtimeAtCoface stage).tick.generated.wholeLedgerWriteBack =
        .transfer (runtimeAtCoface stage).emittedOccurrence.2.write := by
  rfl

def blockReadAfter (prior : UnitHistory) :
    IntegralRelationOperatorCokernel prior.cardinalShadow :=
  match blockComponent.outcomeAt PUnit.unit (emitted (.next prior)) with
  | .inl ⟨_, payload⟩ => payload.2.2
  | .inr inactive => PEmpty.elim inactive

theorem blockReadAfter_original (prior : UnitHistory) :
    blockReadAfter prior =
      blockRelationActionCokernelArithmeticRead prior.cardinalShadow
        (localEndpointBoundaryCokernelClass prior.cardinalShadow) := by
  rfl

theorem blockReadAfter_nonzero (older : UnitHistory) :
    blockReadAfter (.next older) ≠ 0 := by
  rw [blockReadAfter_original]
  exact every_later_original_block_read_nonzero older.cardinalShadow

theorem blockReadAfter_installed (prior : UnitHistory) :
    HEq (facade.readoutAt (runtimeAtCoface prior.cardinalShadow)
        (.component PUnit.unit))
      (blockComponent.outcomeAt PUnit.unit (emitted (.next prior))) := by
  have h := all_later_readout_is_source prior.cardinalShadow
  rw [runtime_current_eq_next prior] at h
  exact h

theorem every_later_block_read_after (older : UnitHistory) :
    blockReadAfter (.next older) =
        blockRelationActionCokernelArithmeticRead (older.cardinalShadow + 1)
          (localEndpointBoundaryCokernelClass (older.cardinalShadow + 1)) ∧
      blockReadAfter (.next older) ≠ 0 ∧
      HEq (facade.readoutAt (runtimeAtCoface (older.cardinalShadow + 1))
          (.component PUnit.unit))
        (blockComponent.outcomeAt PUnit.unit
          (emitted (.next (.next older)))) := by
  exact ⟨blockReadAfter_original (.next older),
    blockReadAfter_nonzero older, blockReadAfter_installed (.next older)⟩

theorem all_later_whole_ledger_same (stage : Nat) :
    HEq (runtimeAtCoface stage).tick.generated.wholeLedgerWriteBack
      (runtimeAt stage).tick.generated.wholeLedgerWriteBack := by
  change HEq
    (authoritativeCoface.toLedgerRoot.generatedLedgerAt
      (runtimeAtCoface stage).current.visit.current)
    (authoritativeRoot.toLedgerRoot.generatedLedgerAt
      (runtimeAt stage).current.visit.current)
  rw [same_current stage]
  rfl

theorem all_later_next_same (stage : Nat) :
    (runtimeAtCoface stage).tick.next.current.visit.current =
      (runtimeAt stage).tick.next.current.visit.current := by
  change next (runtimeAtCoface stage).current.visit.current =
    next (runtimeAt stage).current.visit.current
  exact congrArg next (same_current stage)

theorem original_transfer_disposition_all (stage : Nat) :
    let runtime := runtimeAtCoface stage
    let current := runtime.current.visit.current
    let receipt : RootDispositionAt current .transfer :=
      .transfer runtime.emittedOccurrence.2.write
    HEq (runtime.tick.generated.wholeLedgerWriteBack.entryDisposition
      (rootLedgerEntry current))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred receipt
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt N (rootLedgerEntry current)
              (rootLedgerEntry (next current)))) := by
  rfl

theorem every_later_installed_block_original_consumer_ledger_next
    (older : UnitHistory) :
    let stage := older.cardinalShadow + 1
    let runtime := runtimeAtCoface stage
    let current := runtime.current.visit.current
    blockReadAfter (.next older) =
        blockRelationActionCokernelArithmeticRead stage
          (localEndpointBoundaryCokernelClass stage) ∧
      blockReadAfter (.next older) ≠ 0 ∧
      HEq (facade.readoutAt runtime (.component PUnit.unit))
        (blockComponent.outcomeAt PUnit.unit
          (emitted (.next (.next older)))) ∧
      receiptFromGenerated runtime.tick.generated.wholeLedgerWriteBack =
        .transfer runtime.emittedOccurrence.2.write ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtimeAt stage).tick.generated.wholeLedgerWriteBack ∧
      HEq (runtime.tick.generated.wholeLedgerWriteBack.entryDisposition
        (rootLedgerEntry current))
        (LedgerEntryDispositionAt.evolved
          (LedgerEntryEvolutionAt.transferred
            (.transfer runtime.emittedOccurrence.2.write)
              rfl rfl (Nat.le_refl _) :
                LedgerEntryEvolutionAt N (rootLedgerEntry current)
                  (rootLedgerEntry (next current)))) ∧
      runtime.tick.next.current.visit.current =
        (runtimeAt stage).tick.next.current.visit.current := by
  exact ⟨(every_later_block_read_after older).1,
    (every_later_block_read_after older).2.1,
    (every_later_block_read_after older).2.2,
    receiptFromGenerated_coface_runtime _,
    all_later_whole_ledger_same _,
    original_transfer_disposition_all _,
    all_later_next_same _⟩

end
end CanonicalUnitBlockProjectionCoface
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
