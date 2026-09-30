import H0mework.Versions.Y.Arithmetic.PrimeShadow.DomainConsumers.CanonicalArithmetic.Relation.NativeReceiptBlockProjectionRuntime

/-!
# The installed block face reaches the original consumer and next

At the actual stage-one visit, the new named face reads the old arithmetic
block-action cokernel value. Its nonzero control, inherited material,
original transfer-row disposition, whole ledger and next current are read
at the same emitted source occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CanonicalUnitBlockProjectionCoface

open ArithmeticGeneration
open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitNativeReceiptFactorization
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead

noncomputable section

def blockReadAtOne : IntegralRelationOperatorCokernel 1 :=
  match facade.readoutAt (runtimeAtCoface 1) (.component PUnit.unit) with
  | .inl ⟨_, payload⟩ => payload.2.2
  | .inr inactive => PEmpty.elim inactive

theorem blockReadAtOne_original :
    blockReadAtOne = blockRelationActionCokernelArithmeticRead 1
      (localEndpointBoundaryCokernelClass 1) := by
  rfl

theorem blockReadAtOne_nonzero : blockReadAtOne ≠ 0 := by
  rw [blockReadAtOne_original]
  exact CanonicalUnitNativeReceiptBlockBoundary.receipt_three_nonzero

theorem blockFaceReceiptAtOne :
    match facade.readoutAt (runtimeAtCoface 1) (.component PUnit.unit) with
    | .inl ⟨_, payload⟩ =>
        payload.1 = receiptFromGenerated
          (runtimeAtCoface 1).tick.generated.wholeLedgerWriteBack
    | .inr _ => False := by
  rfl

theorem inherited_material_at_one :
    facade.readoutAt (runtimeAtCoface 1) (.inherited .material) =
      runtimeFacade.readoutAt (runtimeAt 1) .material := by
  rfl

theorem emitted_at_one :
    (runtimeAtCoface 1).emittedOccurrence =
      (runtimeAt 1).emittedOccurrence := by
  rfl

theorem whole_ledger_at_one :
    (runtimeAtCoface 1).tick.generated.wholeLedgerWriteBack =
      (runtimeAt 1).tick.generated.wholeLedgerWriteBack := by
  rfl

theorem next_source_current_at_one :
    (runtimeAtCoface 1).tick.next.current.visit.current =
      (runtimeAt 1).tick.next.current.visit.current := by
  rfl

theorem original_transfer_disposition_at_one :
    let runtime := runtimeAtCoface 1
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

theorem installed_block_original_consumer_ledger_next :
    blockReadAtOne = blockRelationActionCokernelArithmeticRead 1
        (localEndpointBoundaryCokernelClass 1) ∧
      blockReadAtOne ≠ 0 ∧
      (match facade.readoutAt (runtimeAtCoface 1) (.component PUnit.unit) with
        | .inl ⟨_, payload⟩ =>
            payload.1 = receiptFromGenerated
              (runtimeAtCoface 1).tick.generated.wholeLedgerWriteBack
        | .inr _ => False) ∧
      facade.readoutAt (runtimeAtCoface 1) (.inherited .material) =
        runtimeFacade.readoutAt (runtimeAt 1) .material ∧
      HEq (facade.readoutAt (runtimeAtCoface 1) (.component PUnit.unit))
        ((runtimeAtCoface 1).tick.generated.projectionOutcome
          ((facade.installationAt (runtimeAtCoface 1)
            (.component PUnit.unit)).embed
              (facade.projectionAt (runtimeAtCoface 1)
                (.component PUnit.unit)))) ∧
      (runtimeAtCoface 1).tick.generated.wholeLedgerWriteBack =
        (runtimeAt 1).tick.generated.wholeLedgerWriteBack ∧
      HEq ((runtimeAtCoface 1).tick.generated.wholeLedgerWriteBack.entryDisposition
        (rootLedgerEntry (runtimeAtCoface 1).current.visit.current))
        (LedgerEntryDispositionAt.evolved
          (LedgerEntryEvolutionAt.transferred
            (.transfer (runtimeAtCoface 1).emittedOccurrence.2.write)
              rfl rfl (Nat.le_refl _) :
                LedgerEntryEvolutionAt N
                  (rootLedgerEntry (runtimeAtCoface 1).current.visit.current)
                  (rootLedgerEntry
                    (next (runtimeAtCoface 1).current.visit.current)))) ∧
      (runtimeAtCoface 1).tick.next.current.visit.current =
        (runtimeAt 1).tick.next.current.visit.current := by
  exact ⟨blockReadAtOne_original, blockReadAtOne_nonzero,
    blockFaceReceiptAtOne,
    inherited_material_at_one,
    (facade.readoutAt_factorizes (runtimeAtCoface 1)
      (.component PUnit.unit)).2.2.2.1,
    whole_ledger_at_one, original_transfer_disposition_at_one,
    next_source_current_at_one⟩

end
end CanonicalUnitBlockProjectionCoface
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
