import H0mework.Versions.Y.Arithmetic.PrimeShadow.DomainConsumers.CanonicalArithmetic.Relation.NativeReceiptBlockBoundary
import H0mework.Realization.Faces.ProjectionCoface

/-!
# The original unit event generates an installed block dependent face

For a nonempty original unit current, the actual event's transfer receipt
computes the next history. The source history's cardinality identifies its
unique canonical stage; the block read is attached to that same target.
The empty current stays inactive. No block result or branch is an input.
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

def Active : Current → Type
  | .empty => PEmpty
  | .next _ => PUnit

def Inactive : Current → Type
  | .empty => PUnit
  | .next _ => PEmpty

def Payload : Current → Type
  | .empty => PEmpty
  | .next prior =>
      Σ receipt : RootDispositionAt (.next prior) .transfer,
        PLift (transferActionTarget receipt =
          StageHistory seedOccurrence.root prior.cardinalShadow) ×
        IntegralRelationOperatorCokernel prior.cardinalShadow

theorem runtime_current_eq_next (prior : UnitHistory) :
    (runtimeAt prior.cardinalShadow).current.visit.current = .next prior := by
  apply UnitHistory.eq_of_cardinalShadow_eq
  have hwhole := runtimeWholeHistory_cardinalShadow prior.cardinalShadow
  change Nat.succ
    (runtimeAt prior.cardinalShadow).current.visit.current.cardinalShadow =
      prior.cardinalShadow + 2 at hwhole
  change (runtimeAt prior.cardinalShadow).current.visit.current.cardinalShadow =
    prior.cardinalShadow + 1
  omega

theorem transfer_target_eq_next {current : Current}
    (receipt : RootDispositionAt current .transfer) :
    transferActionTarget receipt = next current := by
  cases receipt with
  | transfer write =>
      exact write.target_action_eq.symm.trans write.target_eq

theorem stageHistory_eq_next_current (prior : UnitHistory) :
    StageHistory seedOccurrence.root prior.cardinalShadow = next (.next prior) := by
  rw [stageHistory_eq_runtimeWholeHistory]
  change next (runtimeAt prior.cardinalShadow).current.visit.current = _
  rw [runtime_current_eq_next]

/-- Decode the actual write from the fixed source's generated whole-ledger
branch. The other branches are uninhabited in this original vocabulary. -/
def receiptFromGenerated {current : Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence) :
    RootDispositionAt current .transfer :=
  match generated with
  | .nativeWrite write _ _ _ => .transfer write
  | .relationWrite write _ _ _ => PEmpty.elim write
  | .continuedTransport write _ _ _ => PEmpty.elim write
  | .borromeanRedirect write _ _ _ => PEmpty.elim write
  | .faithfulTerminal terminal _ _ => PEmpty.elim terminal

theorem receiptFromGenerated_compiler {current : Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    receiptFromGenerated (ledgerSource.ledgerCompiler.compile occurrence) =
      .transfer occurrence.2.write := by
  rcases occurrence with ⟨support, ⟨support_eq, trace, trace_eq⟩⟩
  cases support_eq
  cases trace_eq
  rfl

def blockComponent : SourceNativeProjectionLaw ledgerSource where
  Projection := PUnit
  ActiveAt := fun _ {current} _ => Active current
  InactiveAt := fun _ {current} _ => Inactive current
  classify := by
    intro _ current occurrence
    cases current with
    | empty => exact .inr PUnit.unit
    | next prior => exact .inl PUnit.unit
  PayloadAt := fun _ {current} _ _ => Payload current
  project := by
    intro _ current occurrence active
    cases current with
    | empty => exact PEmpty.elim active
    | next prior =>
        let receipt : RootDispositionAt (.next prior) .transfer :=
          receiptFromGenerated (ledgerSource.ledgerCompiler.compile occurrence)
        have htarget : transferActionTarget receipt =
            StageHistory seedOccurrence.root prior.cardinalShadow := by
          exact (transfer_target_eq_next receipt).trans
            (stageHistory_eq_next_current prior).symm
        exact ⟨receipt, ⟨⟨htarget⟩,
          blockRelationActionCokernelArithmeticRead prior.cardinalShadow
            (localEndpointBoundaryCokernelClass prior.cardinalShadow)⟩⟩

theorem empty_source_block_inactive :
    blockComponent.outcomeAt PUnit.unit (emitted .empty) =
      .inr PUnit.unit :=
  rfl

theorem blockComponent_receipt {prior : UnitHistory}
    (occurrence : source.toRootSource.actual.OccurrenceAt (.next prior)) :
    (blockComponent.project PUnit.unit occurrence PUnit.unit).1 =
      receiptFromGenerated (ledgerSource.ledgerCompiler.compile occurrence) :=
  rfl

end
end CanonicalUnitBlockProjectionCoface
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
