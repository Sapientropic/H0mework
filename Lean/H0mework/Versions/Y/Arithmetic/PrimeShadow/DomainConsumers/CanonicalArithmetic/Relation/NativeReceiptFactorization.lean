import H0mework.Versions.Y.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticFactorizationInverseFibreConsumer

/-!
# Complete factorization from the original native transfer receipt

The original unit receipt already contains the executable action tree.  Its
fold target determines the entire dependent prime-power inventory, so the
existing factorization and whole-history equation can be read from that
receipt without storing a second factorization or changing the root law.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CanonicalUnitNativeReceiptFactorization

open ArithmeticGeneration
open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationInverseFibre
open CanonicalUnitArithmeticFactorizationInverseFibreConsumer
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier

noncomputable section

/-- Eliminate the original transfer constructor to recover its actual source
action target.  No alternate material or target is accepted. -/
def transferActionTarget {current : Current}
    (receipt : RootDispositionAt current .transfer) : UnitHistory :=
  match receipt with
  | .transfer write => nativeActionTarget write.actionTrace

def transferFactorization {current : Current}
    (receipt : RootDispositionAt current .transfer) : ℕ →₀ ℕ :=
  factorization (transferActionTarget receipt)

abbrev TransferFactorKey {current : Current}
    (receipt : RootDispositionAt current .transfer) : Type :=
  (index : PrimeIndex (transferActionTarget receipt)) ×
    ExponentIndex (transferActionTarget receipt) index

/-- Every factor key obtained from the actual transfer has the original
source-history joint landing. -/
theorem transfer_all_primePowers_joint_landing
    {current : Current} (receipt : RootDispositionAt current .transfer)
    (key : TransferFactorKey receipt) :
    factorialHistory (transferActionTarget receipt) =
      (primePowerHistory key.1 key.2).joint
        (quotientHistory key.1 key.2) :=
  primePower_joint_landing key.1 key.2

def runtimeReceipt (stage : Nat) :
    RootDispositionAt (runtimeAt stage).current.visit.current .transfer :=
  .transfer (runtimeAt stage).emittedOccurrence.2.write

theorem runtimeReceipt_action_target (stage : Nat) :
    transferActionTarget (runtimeReceipt stage) =
      authorityWholeHistory (factorizationOccurrence stage).root.1 :=
  rfl

theorem stageHistory_eq_runtimeWholeHistory (stage : Nat) :
    StageHistory seedOccurrence.root stage = runtimeWholeHistory stage := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      rw [stageHistory_succ, runtimeWholeHistory_succ,
        inductionHypothesis]

theorem stageHistory_eq_transfer_target (stage : Nat)
    (receipt : RootDispositionAt
      (runtimeAt stage).current.visit.current .transfer) :
    StageHistory seedOccurrence.root stage =
      transferActionTarget receipt := by
  cases receipt with
  | transfer write =>
      rw [stageHistory_eq_runtimeWholeHistory]
      change next (runtimeAt stage).current.visit.current =
        nativeActionTarget write.actionTrace
      exact write.target_eq.symm.trans write.target_action_eq

def rowOfReceiptKey (stage : Nat)
    (receipt : RootDispositionAt
      (runtimeAt stage).current.visit.current .transfer)
    (key : TransferFactorKey receipt) :
    FactorRow seedOccurrence.root stage := by
  change (index : PrimeIndex (StageHistory seedOccurrence.root stage)) ×
    ExponentIndex (StageHistory seedOccurrence.root stage) index
  rw [stageHistory_eq_transfer_target stage receipt]
  exact key

/-- The old transfer's actual factor keys index the already generated common
whole-history equation; no independent factor table enters the equation. -/
theorem transferReceipt_common_equation (stage : Nat)
    (receipt : RootDispositionAt
      (runtimeAt stage).current.visit.current .transfer)
    (base : DualBase) (key : TransferFactorKey receipt) :
    factorizationEquation seedOccurrence.root stage
        (solutionVertex seedOccurrence.root stage base)
        (rowOfReceiptKey stage receipt key) = 0 := by
  rw [factorizationEquation_solutionVertex_eq_zero]
  rfl

/-- The inventory in the literal native transfer is exactly the already
generated complete factorization inventory at the same runtime occurrence. -/
theorem runtimeReceipt_complete_inventory (stage : Nat) :
    (transferFactorization (runtimeReceipt stage)).support =
      (factorizationOccurrence stage).root.2.primeSupport :=
  rfl

theorem runtimeReceipt_keyTwo_and_keyThree :
    let receipt := runtimeReceipt 1
    (keyTwo : TransferFactorKey receipt) ≠
      (keyThree : TransferFactorKey receipt) ∧
      factorialHistory (transferActionTarget receipt) =
        (primePowerHistory keyTwo.1 keyTwo.2).joint
          (quotientHistory keyTwo.1 keyTwo.2) ∧
      factorialHistory (transferActionTarget receipt) =
        (primePowerHistory keyThree.1 keyThree.2).joint
          (quotientHistory keyThree.1 keyThree.2) := by
  dsimp
  exact ⟨keyTwo_ne_keyThree,
    transfer_all_primePowers_joint_landing (runtimeReceipt 1) keyTwo,
    transfer_all_primePowers_joint_landing (runtimeReceipt 1) keyThree⟩

/-- The same transfer receipt is the old whole-ledger row's actual payload.
The resulting factor inventory is consumed by the existing common equation;
the root compiler still generates the literal next current. -/
theorem runtimeReceipt_inventory_ledger_equation_next (stage : Nat) :
    let runtime := runtimeAt stage
    let current := runtime.current.visit.current
    let receipt := runtimeReceipt stage
    (transferFactorization receipt).support =
        (factorizationOccurrence stage).root.2.primeSupport ∧
      (∀ key : TransferFactorKey receipt,
        factorialHistory (transferActionTarget receipt) =
          (primePowerHistory key.1 key.2).joint
            (quotientHistory key.1 key.2)) ∧
      (∀ base : DualBase, ∀ key : TransferFactorKey receipt,
        factorizationEquation seedOccurrence.root stage
          (solutionVertex seedOccurrence.root stage base)
          (rowOfReceiptKey stage receipt key) = 0) ∧
      HEq (runtime.tick.generated.wholeLedgerWriteBack.entryDisposition
        (rootLedgerEntry current))
        (LedgerEntryDispositionAt.evolved
          (LedgerEntryEvolutionAt.transferred receipt
            rfl rfl (Nat.le_refl _) :
              LedgerEntryEvolutionAt N (rootLedgerEntry current)
                (rootLedgerEntry (next current)))) ∧
      runtime.tick.nextCurrent =
        runtimeFacade.process.stateAt
          (runtimeFacade.process.successor runtime.state) := by
  refine ⟨runtimeReceipt_complete_inventory stage,
    transfer_all_primePowers_joint_landing (runtimeReceipt stage),
    transferReceipt_common_equation stage (runtimeReceipt stage), ?_,
    (runtime_authority_factorizes stage).2.2⟩
  dsimp [runtimeReceipt]
  rfl

end
end CanonicalUnitNativeReceiptFactorization
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
