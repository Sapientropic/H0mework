import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Source
import H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel

/-! The actual first execution step jointly pays its own row and preserves
the original native write, complete paired value and generated next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculation

open SourceOperationEffects SourceOperationNative SourceOperationExecution
open SourceOperationInventoryLift DebtActivationWorld DebtActivationLedger
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationDerivation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

noncomputable section

def baseCurrent (runtime : LivingRuntimeState process) : CanonicalUnitArithmeticRoot.Current :=
  runtime.current.visit.current

def wholeBase (runtime : LivingRuntimeState process) :
    LedgerWriteEvolutionAt CanonicalUnitArithmeticRoot.N ⟨baseCurrent runtime⟩
      ⟨CanonicalUnitArithmeticRoot.next (baseCurrent runtime)⟩ :=
  (CanonicalUnitArithmeticRoot.generatedPatchAtOccurrence
    (CanonicalUnitArithmeticRoot.emitted (baseCurrent runtime))).toLedgerWriteEvolution

def jointPayment (runtime : LivingRuntimeState process) :=
  jointStepLedgerEvolution (wholeBase runtime)
    (CanonicalUnitArithmeticRoot.rootLedgerEntry (baseCurrent runtime)) (firstStep runtime).2

theorem raw_value (runtime : LivingRuntimeState process) :
    rawExpression.eval (rawEnvironment runtime) =
      ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) := by
  exact (Context.embed_eval SourcePhysicalContextRelationConsumer.readPaired
    (liftExpr fockOperation) runtime).trans
    ((congrArg (fun environment => (liftExpr fockOperation).eval environment)
      (SourcePhysicalContextRelationConsumer.readPaired_actual runtime)).trans
        (stage_lift_read (SourceGeneratedRuntimeMaterialStageAt.generate runtime)))

theorem firstStep_value (runtime : LivingRuntimeState process) :
    (paidState runtime).1.eval (rawEnvironment runtime) =
      ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) :=
  (paidState runtime).2.sound.symm.trans (raw_value runtime)

theorem completed_value (runtime : LivingRuntimeState process)
    (state : (calculationLaw runtime).DebtState)
    (settled : (calculationLaw runtime).SettlementAt state) :
    settled.1 = ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) :=
  (SourceOperationExecutionDebt.completed_value state settled).trans (raw_value runtime)

theorem original_occurrence (runtime : LivingRuntimeState process) :
    runtime.emittedOccurrence = CanonicalUnitArithmeticRoot.emitted (baseCurrent runtime) :=
  canonicalOccurrence_unique _ _

theorem original_next (runtime : LivingRuntimeState process) :
    CanonicalUnitArithmeticRoot.next (baseCurrent runtime) = baseCurrent runtime.tick.next := rfl

theorem wholeBase_native_evolution (runtime : LivingRuntimeState process) :
    HEq ((wholeBase runtime).destination
      (CanonicalUnitArithmeticRoot.rootLedgerEntry (baseCurrent runtime))).2
      (.transferred
        (CanonicalUnitArithmeticRoot.RootDispositionAt.transfer
          (CanonicalUnitArithmeticRoot.emitted (baseCurrent runtime)).2.write)
        rfl rfl (Nat.le_refl _) : LedgerEntryEvolutionAt CanonicalUnitArithmeticRoot.N
          (CanonicalUnitArithmeticRoot.rootLedgerEntry (baseCurrent runtime))
          (CanonicalUnitArithmeticRoot.rootLedgerEntry (CanonicalUnitArithmeticRoot.next (baseCurrent runtime)))) := by
  rfl

theorem jointPayment_old_destination (runtime : LivingRuntimeState process)
    (entry : OpenResponsibilityAt CanonicalUnitArithmeticRoot.N (baseCurrent runtime)) :
    ((jointPayment runtime).destination
      (oldEntry (law := calculationLaw runtime) (state? := some (initial runtime)) entry)).1 =
        oldEntry (law := calculationLaw runtime) (state? := some (paidState runtime))
          (wholeBase runtime |>.destination entry).1 := rfl

theorem jointPayment_math_destination (runtime : LivingRuntimeState process) :
    ((jointPayment runtime).destination
      (debtEntry (N := CanonicalUnitArithmeticRoot.N) (baseCurrent runtime) (initial runtime))).1 =
        debtEntry (N := CanonicalUnitArithmeticRoot.N)
          (CanonicalUnitArithmeticRoot.next (baseCurrent runtime)) (paidState runtime) := rfl

theorem jointPayment_math_strict (runtime : LivingRuntimeState process) :
    ((jointPayment runtime).destination
      (debtEntry (N := CanonicalUnitArithmeticRoot.N) (baseCurrent runtime) (initial runtime))).1.progressBudget <
        (debtEntry (N := CanonicalUnitArithmeticRoot.N) (baseCurrent runtime) (initial runtime)).progressBudget :=
  jointStepLedgerEvolution_debt_strict (wholeBase runtime)
    (CanonicalUnitArithmeticRoot.rootLedgerEntry (baseCurrent runtime)) (firstStep runtime).2

theorem runtime_firstStep_jointPayment_ledger_next (depth : Nat) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    (calculationLaw runtime).budget (initial runtime) = 10 ∧
    (calculationLaw runtime).budget (paidState runtime) = 9 ∧
    (paidState runtime).1.eval (rawEnvironment runtime) =
      ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) ∧
    ((jointPayment runtime).destination
      (debtEntry (N := CanonicalUnitArithmeticRoot.N) (baseCurrent runtime) (initial runtime))).1 =
        debtEntry (N := CanonicalUnitArithmeticRoot.N)
          (baseCurrent runtime.tick.next) (paidState runtime) ∧
    ((jointPayment runtime).destination
      (debtEntry (N := CanonicalUnitArithmeticRoot.N) (baseCurrent runtime) (initial runtime))).1.progressBudget <
        (debtEntry (N := CanonicalUnitArithmeticRoot.N) (baseCurrent runtime) (initial runtime)).progressBudget ∧
    runtimeFacade.readoutAt runtime .particleWave = .inl ⟨activeAt runtime, payloadAt runtime⟩ ∧
    stage.activated.generated.occurrence =
      runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
    HEq stage.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    stage.next.current = stage.activated.nextCurrent := by
  dsimp only
  obtain ⟨_, readout, occurrence, _installed, ledger, sameNext⟩ :=
    stage_source_factorizes (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth))
  refine ⟨initial_budget _, paid_budget _, firstStep_value _, ?_, jointPayment_math_strict _,
    readout, occurrence, ledger, sameNext⟩
  exact jointPayment_math_destination (runtimeAt depth)

end
end SourcePhysicalCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
