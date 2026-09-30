import H0mework.Versions.Y.Arithmetic.PrimeShadow.DomainConsumers.CanonicalArithmetic.Relation.NativeReceiptJointConsumerCoimage

/-!
# The original block boundary survives every generated unit successor

The stage-one native receipt creates the prime-three row and a nonzero
arithmetic block-action class. The existing exact restriction of the endpoint
class then transports nonvanishing forward through every later canonical
runtime visit. At each visit the original transfer row, installed material,
whole ledger, and literal next are read from the same source compiler.
-/

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CanonicalUnitNativeReceiptBlockBoundaryPersistence

open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitNativeReceiptFactorization
open CanonicalUnitNativeReceiptBlockBoundary
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelNaturality

noncomputable section

theorem every_later_integral_class_nonzero (offset : Nat) :
    specializedIntegralEndpointBoundaryClass (offset + 1) ≠ 0 := by
  induction offset with
  | zero =>
      simpa only [Nat.zero_add] using
        (show specializedIntegralEndpointBoundaryClass 1 ≠ 0 by
          rw [← blockRelationActionCokernelArithmeticRead_endpointClass]
          exact receipt_three_nonzero)
  | succ offset ih =>
      intro vanished
      have projected := congrArg
        (integralRelationOperatorCokernelRestriction (offset + 1)) vanished
      rw [map_zero, integralRelationOperatorCokernelRestriction_endpointClass]
        at projected
      exact ih projected

theorem every_later_original_block_read_nonzero (offset : Nat) :
    blockRelationActionCokernelArithmeticRead (offset + 1)
      (localEndpointBoundaryCokernelClass (offset + 1)) ≠ 0 := by
  rw [blockRelationActionCokernelArithmeticRead_endpointClass]
  exact every_later_integral_class_nonzero offset

theorem every_later_original_ledger_next (offset : Nat) :
    let stage := offset + 1
    let runtime := runtimeAt stage
    let current := runtime.current.visit.current
    let receipt := runtimeReceipt stage
    installedMaterialWhole stage = transferActionTarget receipt ∧
      runtime.tick.generated.occurrence =
        runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted current ∧
      HEq (runtimeFacade.readoutAt runtime .material)
        (runtime.tick.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .material).embed
            (runtimeFacade.projectionAt runtime .material))) ∧
      blockRelationActionCokernelArithmeticRead stage
        (localEndpointBoundaryCokernelClass stage) ≠ 0 ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current) ∧
      HEq (runtime.tick.generated.wholeLedgerWriteBack.entryDisposition
        (rootLedgerEntry current))
        (LedgerEntryDispositionAt.evolved
          (LedgerEntryEvolutionAt.transferred receipt
            rfl rfl (Nat.le_refl _) :
              LedgerEntryEvolutionAt N (rootLedgerEntry current)
                (rootLedgerEntry (next current)))) ∧
      runtime.tick.next = runtimeAt (stage + 1) ∧
      runtime.tick.nextCurrent =
        runtimeFacade.process.stateAt
          (runtimeFacade.process.successor runtime.state) := by
  dsimp only
  exact ⟨installedMaterialWhole_eq_receiptTarget (offset + 1),
    (coversAt_factorizes (runtimeAt (offset + 1)) .material).2.1,
    (coversAt_factorizes (runtimeAt (offset + 1)) .material).2.2.2.1,
    every_later_original_block_read_nonzero offset,
    (coversAt_factorizes (runtimeAt (offset + 1)) .material).2.2.1,
    (runtimeReceipt_inventory_ledger_equation_next (offset + 1)).2.2.2.1,
    rfl,
    (runtimeReceipt_inventory_ledger_equation_next (offset + 1)).2.2.2.2⟩

end
end CanonicalUnitNativeReceiptBlockBoundaryPersistence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
