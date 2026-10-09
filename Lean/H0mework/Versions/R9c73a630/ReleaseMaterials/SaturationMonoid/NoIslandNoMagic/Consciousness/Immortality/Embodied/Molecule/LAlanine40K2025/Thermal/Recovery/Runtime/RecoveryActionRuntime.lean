import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Runtime.RecoveryActionProgram

/-! # One recovery ingress and ordinary load continuation use the existing canonical runtime -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Propagation.Producer Load.Source Load.Producer Load.Producer.RecoveryLedger Recovery.Producer Recovery.StrictRefill

noncomputable section

theorem recoveryRuntimeRoot_generated : generatedRecoveryAction.target.targetRoot = recoveryLivingRoot := rfl

def recoveryProcessCurrent (visit : RootVisit recoveryLivingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt RecoveryN := ⟨RecoveryV, recoveryLivingRoot, .finite visit⟩

def recoveryRuntimeProcess : SourceNativeLivingRootProcess RecoveryN where
  State := RootVisit recoveryLivingRoot.toAuthoritativeRoot.toRoot
  stateAt := recoveryProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨RecoveryV, recoveryLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt RecoveryN) =
      ⟨RecoveryV, recoveryLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := recoveryLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := fun visit => ⟨visit.next rfl, rfl, HEq.rfl⟩

def recoveryRuntimeFacade : SourceNativeLivingRuntimeFacade RecoveryN where
  process := recoveryRuntimeProcess
  FaceAt := fun _ => RecoveryProjection
  componentAt := fun _ _ => recoveryProjectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def recoveryRuntimeSeed : LivingRuntimeState recoveryRuntimeProcess := recoveryRuntimeFacade.seed

def recoveryRuntimeAfterFirst : LivingRuntimeState recoveryRuntimeProcess := recoveryRuntimeSeed.tick.next

theorem recoveryRuntimeFirst_is_generated_action :
    recoveryCurrentState recoveryRuntimeAfterFirst.state.current = generatedRecoveryAction.answer := rfl

theorem recoveryRuntimeNext_received (runtime : LivingRuntimeState recoveryRuntimeProcess) :
    recoveryCurrentState runtime.tick.next.state.current =
      recoveryCurrentState (recoveryNext runtime.state.current) := rfl

theorem recoveryRuntime_next_is_load (runtime : LivingRuntimeState recoveryRuntimeProcess) :
    recoveryCurrentState runtime.tick.next.tick.next.state.current =
      loadStateNext (recoveryCurrentState runtime.tick.next.state.current) := rfl

theorem recoveryRuntimeNext_joint (runtime : LivingRuntimeState recoveryRuntimeProcess) :
    (recoveryCurrentState runtime.tick.next.state.current).joint =
      Thermal.Quantum.conjugation (recoveryControlRead runtime.state.current).action
        (recoveryCurrentState runtime.state.current).joint :=
  recoveryNext_joint runtime.state.current

theorem recoveryRuntime_nextClock (runtime : LivingRuntimeState recoveryRuntimeProcess) :
    (recoveryCurrentState runtime.tick.next.state.current).localClock =
      (recoveryCurrentState runtime.state.current).localClock +
        (recoveryControlRead runtime.state.current).duration := recoveryNext_clock runtime.state.current

theorem recoveryRuntime_firstClock :
    (recoveryCurrentState recoveryRuntimeAfterFirst.state.current).localClock = 4 * nativeClockStep := by
  change (0 + nativeClockStep) + 3 * nativeClockStep = 4 * nativeClockStep
  ring

theorem recoveryRuntime_netAccount (runtime : LivingRuntimeState recoveryRuntimeProcess) :
    (loadBindingAccountedFreeEnergy (recoveryCurrentState runtime.tick.next.state.current) -
      loadBindingAccountedFreeEnergy (recoveryCurrentState runtime.state.current)) +
      (loadEntropyProduction (recoveryCurrentState runtime.tick.next.state.current) -
        loadEntropyProduction (recoveryCurrentState runtime.state.current)) =
      recoveryEventWork runtime.state.current := recoveryNext_netAccount runtime.state.current

/-- The existing history transports a single ingress work payment from the original load origin. -/
theorem recoveryRuntime_entropyPaid (runtime : LivingRuntimeState recoveryRuntimeProcess) :
    loadEntropyProduction (recoveryCurrentState runtime.state.current) +
      loadBindingAccountedFreeEnergy (recoveryCurrentState runtime.state.current) =
      loadBindingAccountedFreeEnergy loadInitialState + recoveryAccumulatedWork runtime.state.current := by
  have paid (state : recoveryRuntimeProcess.State)
      (reachable : SourceNativeRuntimeReachableAt recoveryRuntimeProcess state) :
      loadEntropyProduction (recoveryCurrentState state.current) +
        loadBindingAccountedFreeEnergy (recoveryCurrentState state.current) =
        loadBindingAccountedFreeEnergy loadInitialState + recoveryAccumulatedWork state.current := by
    induction reachable with
    | initial =>
      change loadEntropyProduction recoveryReceivedState + loadBindingAccountedFreeEnergy recoveryReceivedState =
        loadBindingAccountedFreeEnergy loadInitialState + 0
      have parentPaid := Load.Runtime.loadRuntime_entropyPaid Load.Runtime.loadRuntimeAfterFirst
      change loadEntropyProduction recoveryReceivedState =
        loadBindingAccountedFreeEnergy loadInitialState - loadBindingAccountedFreeEnergy recoveryReceivedState at parentPaid
      linarith
    | @step state _ prior =>
      change loadEntropyProduction (recoveryCurrentState (recoveryNext state.current)) +
        loadBindingAccountedFreeEnergy (recoveryCurrentState (recoveryNext state.current)) =
        loadBindingAccountedFreeEnergy loadInitialState + recoveryAccumulatedWork (recoveryNext state.current)
      have accrued := recoveryAccumulatedWork_next state.current
      have balance := recoveryNext_netAccount state.current
      linarith
  exact paid runtime.state runtime.reachable

theorem recoveryRuntime_paidDebit_nonnegative (runtime : LivingRuntimeState recoveryRuntimeProcess) :
    0 ≤ loadBindingAccountedFreeEnergy loadInitialState + recoveryAccumulatedWork runtime.state.current -
      loadBindingAccountedFreeEnergy (recoveryCurrentState runtime.state.current) := by
  have paid := recoveryRuntime_entropyPaid runtime
  have positive := loadEntropy_nonnegative (recoveryCurrentState runtime.state.current)
  linarith

theorem recoveryRuntimeFace_factorizes (runtime : LivingRuntimeState recoveryRuntimeProcess)
    (projection : RecoveryProjection) :
    type_of% (recoveryRuntimeFacade.readoutAt_factorizes runtime projection) :=
  recoveryRuntimeFacade.readoutAt_factorizes runtime projection

theorem recoveryRuntime_face_is_installed (runtime : LivingRuntimeState recoveryRuntimeProcess)
    (projection : RecoveryProjection) :
    recoveryRuntimeFacade.readoutAt runtime projection =
      recoveryProjectionLaw.outcomeAt projection (recoveryEmitted runtime.state.current) := rfl

theorem recoveryRuntime_netAccount_is_installed (runtime : LivingRuntimeState recoveryRuntimeProcess) :
    recoveryRuntimeFacade.readoutAt runtime .netAccount =
      (.inl ⟨PUnit.unit, (recoveryEventWork runtime.state.current,
        recoveryAccumulatedWork runtime.state.current, ⟨recoveryNext_netAccount runtime.state.current⟩)⟩ :
        SourceNativeProjectionFiberAt recoveryProjectionLaw .netAccount
          (recoveryEmitted runtime.state.current)) := rfl

theorem recoveryRuntime_wholeLedger_is_installed (runtime : LivingRuntimeState recoveryRuntimeProcess) :
    recoveryRuntimeFacade.readoutAt runtime .wholeLedger =
      (.inl ⟨PUnit.unit, recoveryLedgerCompiler.compile (recoveryEmitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt recoveryProjectionLaw .wholeLedger
          (recoveryEmitted runtime.state.current)) := rfl

theorem recoveryRuntime_firstRecovery_is_installed :
    recoveryRuntimeFacade.readoutAt recoveryRuntimeSeed .firstRecovery =
      (.inl ⟨PUnit.unit, ⟨sourceGeneratedRecovery, sourceGeneratedStrictRefill, recoveryStep_entropy recoveryReceivedState,
        recoveryStep_gibbs recoveryReceivedState, recoveryStep_environmentEnergy recoveryReceivedState⟩⟩ :
        SourceNativeProjectionFiberAt recoveryProjectionLaw .firstRecovery (recoveryEmitted .ingress)) := rfl

theorem recoveryRuntime_nextRecovery_is_inactive (runtime : LivingRuntimeState recoveryRuntimeProcess) :
    recoveryRuntimeFacade.readoutAt runtime.tick.next .firstRecovery =
      (.inr PUnit.unit : SourceNativeProjectionFiberAt recoveryProjectionLaw .firstRecovery
          (recoveryEmitted runtime.tick.next.state.current)) := rfl

theorem recoveryRuntime_strictRefill :
    type_of% (recoveryRuntimeFace_factorizes recoveryRuntimeSeed .firstRecovery) ∧
    type_of% sourceGeneratedStrictRefill := by
  refine ⟨recoveryRuntimeFace_factorizes recoveryRuntimeSeed .firstRecovery, ?_⟩
  rcases recoveryRuntimeFacade.readoutAt recoveryRuntimeSeed .firstRecovery with ⟨_, delivered⟩ | inactive
  · exact delivered.down.2.1
  · exact PEmpty.elim inactive

theorem recoveryRuntime_strictBalances :
    11 * (nativeClockStep : ℝ) ^ 2 / 4 <
      recipientEnergy (recoveryCurrentState recoveryRuntimeAfterFirst.state.current) -
        recipientEnergy (recoveryCurrentState recoveryRuntimeSeed.state.current) ∧
    11 * (nativeClockStep : ℝ) ^ 2 / 4 <
      pairEnergy (recoveryCurrentState recoveryRuntimeSeed.state.current) -
        pairEnergy (recoveryCurrentState recoveryRuntimeAfterFirst.state.current) ∧
    recipientEnergy (recoveryCurrentState recoveryRuntimeAfterFirst.state.current) -
        recipientEnergy (recoveryCurrentState recoveryRuntimeSeed.state.current) =
      pairEnergy (recoveryCurrentState recoveryRuntimeSeed.state.current) -
        pairEnergy (recoveryCurrentState recoveryRuntimeAfterFirst.state.current) := by
  have delivered := recoveryRuntime_strictRefill.2
  exact ⟨delivered.1, delivered.2.2.1, delivered.2.2.2.1⟩

theorem recoveryRuntime_controller_bound :
    2 - 25 * (nativeClockStep : ℝ) ^ 2 / 8 ≤
      recipientEnergy (recoveryCurrentState recoveryRuntimeAfterFirst.state.current) :=
  recoveryStateFirst_controller_bound

theorem recoveryRuntime_capacity_bound :
    2 - 25 * (nativeClockStep : ℝ) ^ 2 / 4 ≤
      Powered.Producer.poweredControllerCapacity (pcRead (recoveryCurrentState recoveryRuntimeAfterFirst.state.current)) :=
  recoveryStateFirst_capacity_bound

theorem recoveryRuntime_signedSupplier_paid :
    recipientEnergy (recoveryCurrentState recoveryRuntimeAfterFirst.state.current) -
      recipientEnergy (recoveryCurrentState recoveryRuntimeSeed.state.current) =
      supplierDebit (recoveryCurrentState recoveryRuntimeSeed.state.current)
        (recoveryCurrentState recoveryRuntimeAfterFirst.state.current) := recoveryStep_recipient_paid recoveryReceivedState

theorem recoveryRuntime_strictCost_retained :
    0 < loadGibbsExcess (recoveryCurrentState recoveryRuntimeAfterFirst.state.current) ∧
      0 < loadEntropyProduction (recoveryCurrentState recoveryRuntimeAfterFirst.state.current) :=
  recoveryStateFirst_strictCost

theorem recoveryRuntime_completeAccount (runtime : LivingRuntimeState recoveryRuntimeProcess) :
    (∀ projection, type_of% (recoveryRuntimeFace_factorizes runtime projection)) ∧
    (∀ projection, type_of% (recoveryRuntime_face_is_installed runtime projection)) ∧
    type_of% (recoveryRuntime_wholeLedger_is_installed runtime) ∧
    type_of% (recoveryRuntime_netAccount_is_installed runtime) ∧
    type_of% (recoveryRuntimeNext_joint runtime) ∧
    type_of% (recoveryRuntime_next_is_load runtime) ∧
    type_of% (recoveryRuntime_netAccount runtime) ∧
    type_of% (recoveryRuntime_entropyPaid runtime) ∧
    type_of% (recoveryRuntime_paidDebit_nonnegative runtime) :=
  ⟨recoveryRuntimeFace_factorizes runtime, recoveryRuntime_face_is_installed runtime,
    recoveryRuntime_wholeLedger_is_installed runtime, recoveryRuntime_netAccount_is_installed runtime,
    recoveryRuntimeNext_joint runtime, recoveryRuntime_next_is_load runtime, recoveryRuntime_netAccount runtime,
    recoveryRuntime_entropyPaid runtime, recoveryRuntime_paidDebit_nonnegative runtime⟩

theorem recoveryRuntime_sourceGeneratedRecovery :
    type_of% (recoveryRuntime_completeAccount recoveryRuntimeSeed) ∧
    type_of% recoveryRuntime_firstRecovery_is_installed ∧
    type_of% recoveryRuntimeFirst_is_generated_action ∧ type_of% generatedRecoveryAction_next ∧
    type_of% recoveryRuntime_controller_bound ∧ type_of% recoveryRuntime_capacity_bound ∧
    type_of% recoveryRuntime_signedSupplier_paid ∧ type_of% recoveryRuntime_strictCost_retained ∧
    type_of% recoveryRuntime_firstClock ∧
    type_of% (recoveryRuntime_nextRecovery_is_inactive recoveryRuntimeSeed) ∧
    type_of% recoveryRuntime_strictBalances :=
  ⟨recoveryRuntime_completeAccount recoveryRuntimeSeed, recoveryRuntime_firstRecovery_is_installed,
    recoveryRuntimeFirst_is_generated_action, generatedRecoveryAction_next, recoveryRuntime_controller_bound,
    recoveryRuntime_capacity_bound, recoveryRuntime_signedSupplier_paid, recoveryRuntime_strictCost_retained,
    recoveryRuntime_firstClock, recoveryRuntime_nextRecovery_is_inactive recoveryRuntimeSeed,
    recoveryRuntime_strictBalances⟩

end

end LAlanine40K2025.Thermal.Recovery.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
