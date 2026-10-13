import H0mework.Realization.SourceComparison.RawConsumption
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.LivingLawRootGeneratedCofinalFaithfulResidualInstalledFaceKernel

/-!
# Cofinal faithful material from an actual raw-dynamics event

The fixed raw root already transfers its exact source event as its old-row
receipt. This law reads seed, continuation and evaluator from that event,
then installs the existing faithful material and residual faces before the
emitter is used. No branch, coverage, residual, target or next is an input.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot
namespace CofinalAction

open CofinalHistorySettlement
open CofinalHistorySettlementFace
open CofinalFaithfulSettlementFace
open CofinalFaithfulResidualInstalledFace
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section

universe u

/-- The source event's complete cofinal action, before classification. -/
structure Law (D : Dynamics.{u}) (Carrier : Type u)
    [AddCommGroup Carrier] : Type (u + 1) where
  Generator : Type u
  rootExposureAt : {state : D.State} →
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) →
      RootedAccountedUnfolding
        ((source D).toRootSource.actual.OccurrenceAt state)
  rootExposure_root : {state : D.State} →
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) →
      (rootExposureAt occurrence).root = occurrence
  seedAt : {state : D.State} → D.EventAt state →
    RootedAccountedUnfolding (PresentedRelationEventAt Generator)
  continuationAt : {state : D.State} → D.EventAt state →
    RootedAccountedUnfolding
      (PresentedRelationEventAt Generator →
        RootedAccountedUnfolding (PresentedRelationEventAt Generator))
  evaluatorAt : {state : D.State} → D.EventAt state →
    RootedAccountedUnfolding (Generator → Carrier)

variable {D : Dynamics.{u}} {Carrier : Type u} [AddCommGroup Carrier]

/-- Eliminate the original source-ledger compiler image. The other structural
branches are empty in this fixed raw-dynamics vocabulary. -/
def receiptFromCompiler {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    D.EventAt state :=
  match (ledgerCompiler D).compile occurrence with
  | .nativeWrite event _ _ _ => event
  | .relationWrite event _ _ _ => PEmpty.elim event
  | .continuedTransport event _ _ _ => PEmpty.elim event
  | .borromeanRedirect event _ _ _ => PEmpty.elim event
  | .faithfulTerminal event _ _ => PEmpty.elim event

theorem receiptFromCompiler_eq_event {state : D.State}
    (event : D.EventAt state) :
    receiptFromCompiler (D := D)
      ((eventPresentation D state).forward event) = event := rfl

def historyLaw (law : Law D Carrier) :
    SourceNativeCofinalHistoryMaterialLaw (restructuringSource D).toLedgerSource :=
  SourceNativeCofinalHistoryMaterialLaw.create law.Generator
    law.rootExposureAt law.rootExposure_root
    (fun occurrence => law.seedAt (receiptFromCompiler (D := D) occurrence))
    (fun occurrence => law.continuationAt (receiptFromCompiler (D := D) occurrence))

def faithfulLaw (law : Law D Carrier) :
    SourceNativeCofinalFaithfulMaterialLaw
      (restructuringSource D).toLedgerSource Carrier :=
  SourceNativeCofinalFaithfulMaterialLaw.create (historyLaw law)
    (fun occurrence => law.evaluatorAt (receiptFromCompiler (D := D) occurrence))

theorem raw_action_eq_event (law : Law D Carrier) {state : D.State}
    (event : D.EventAt state) :
    let occurrence := (eventPresentation D state).forward event
    ((faithfulLaw law).rawAt occurrence).history.rootExposure =
        law.rootExposureAt occurrence ∧
    ((faithfulLaw law).rawAt occurrence).history.seed = law.seedAt event ∧
      ((faithfulLaw law).rawAt occurrence).history.continuation =
        law.continuationAt event ∧
      ((faithfulLaw law).rawAt occurrence).evaluator =
        law.evaluatorAt event := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Install the raw material on the existing generated root's source. -/
def materialSource (law : Law D Carrier) :
    SourceNativeAuthoritySource (network D) (vocabulary D) :=
  ((root D).toAuthoritativeRoot.source).withProjectionCoface
    (faithfulLaw law).toProjectionLaw

def materialRoot (law : Law D Carrier) :
    SourceNativeAuthoritativeRootClosure (network D) (vocabulary D) where
  source := materialSource law
  emitted := emitted D
  compiler_commutes := (root D).toAuthoritativeRoot.compiler_commutes

def materialLivingRoot (law : Law D Carrier) :
    SourceNativeLivingRootClosure (network D) (vocabulary D) :=
  (materialRoot law).toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

def materialInstallation (law : Law D Carrier) :
    SourceNativeProjectionLaw.InstallationAt
      (faithfulLaw law).toProjectionLaw
      (materialSource law).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (root D).toAuthoritativeRoot.source (faithfulLaw law).toProjectionLaw

def recognition (law : Law D Carrier) :
    SourceNativeCofinalFaithfulRecognitionAt Carrier
      (materialLivingRoot law) :=
  SourceNativeCofinalFaithfulRecognitionAt.create
    (faithfulLaw law) (materialInstallation law)

def residualRoot (law : Law D Carrier) :
    SourceNativeAuthoritativeRootClosure (network D) (vocabulary D) :=
  installedRoot (recognition law)

theorem same_lower_root (law : Law D Carrier) :
    (residualRoot law).toLedgerRoot = (root D).toAuthoritativeRoot.toLedgerRoot :=
  rfl

theorem generated_event_ledger_next (law : Law D Carrier) (state : D.State) :
    (residualRoot law).source.projectionLaw.outcomeAt
      (.component PUnit.unit) ((residualRoot law).emitted state) =
        .inl ⟨PUnit.unit,
          ((faithfulLaw law).faithfulAt (emitted D state)).settleWithResidual⟩ ∧
    HEq (((residualRoot law).toLedgerRoot.generatedLedgerAt state).entryDisposition
      (entry D state))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred (D.emit state)
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt (network D)
              (entry D state) (entry D (D.update (D.emit state))))) ∧
    ((residualRoot law).toRoot.evolutionAt state).nextCurrent? =
      some (D.update (D.emit state)) := by
  exact ⟨rfl, HEq.rfl, rfl⟩

/-- The original event's evaluator produces the actual linear equation.
The old row still carries that exact event as its transfer receipt. -/
theorem generated_single_equation (law : Law D Carrier) (state : D.State)
    (generator : law.Generator) (coefficient : ℤ) :
    ((faithfulLaw law).faithfulAt (emitted D state)).freeEvaluation
      (Finsupp.single generator coefficient) =
      coefficient • (law.evaluatorAt (D.emit state)).root generator ∧
    HEq (((residualRoot law).toLedgerRoot.generatedLedgerAt state).entryDisposition
      (entry D state))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred (D.emit state)
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt (network D)
              (entry D state) (entry D (D.update (D.emit state))))) := by
  exact ⟨((faithfulLaw law).faithfulAt (emitted D state)).freeEvaluation_single
    generator coefficient, (generated_event_ledger_next law state).2.1⟩

end
end CofinalAction
end RawGeneratedRoot
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
