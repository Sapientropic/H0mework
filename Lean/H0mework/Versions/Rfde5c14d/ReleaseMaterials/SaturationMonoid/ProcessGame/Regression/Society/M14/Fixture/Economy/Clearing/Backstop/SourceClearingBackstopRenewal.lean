import H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Clearing.Backstop.SourceGeneratedClearingBackstopActivation

/-!
# M14 root-polymorphic clearing-backstop renewal

C5 has already generated the exact residual-consumer occurrence for the
existing `partialOccurrence/.b` responsibility.  This fixture exposes that
single source occurrence as a renewal restriction and applied disposition
which any existing living-law root shell may install before emission.

The local seed and seed law are definitionally the existing backstop
compiler's `ActivationSeed` and `activationSeedAt`.  The fixture does not
accept or store an adapter, edge, next state, root occurrence, row, ledger,
coverage table, schedule, or completed future.  Those are read respectively
from the exact local occurrence and from the later root's existing shell.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceClearingBackstopRenewal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Renewal Clearing
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression
open M4AutomaticFullFulfillmentRegression
open M14ClearingConsumerDeath
open M14SourceGeneratedClearingBackstopActivation

abbrev LocalGame := Lifecycle.actualEventGame
abbrev LocalSeed := partialBResidualConsumerCompiler.ActivationSeed
abbrev LocalSeedAt := partialBResidualConsumerCompiler.activationSeedAt

/-! ## Source restriction and applied disposition -/

/-- The local consumer restriction is indexed by the exact activation seed
read from C5's generated occurrence.  The death cause is the already existing
C4 carrier; it is not reconstructed from the target appearance. -/
structure SourceClearingBackstopRestrictionAt
    (seed : partialBResidualConsumerCompiler.ExactActivationSeed) : Type where
  private mk ::
  seed_eq : seed = sourceGeneratedClearingBackstopExactSeed
  deathCause : Nonempty
    (SourceGeneratedClearingConsumerDeathAt partialOpenB)

/-- Sole source restriction producer. -/
def sourceClearingBackstopRestriction :
    SourceClearingBackstopRestrictionAt
      sourceGeneratedClearingBackstopExactSeed where
  seed_eq := rfl
  deathCause := ⟨sourceGeneratedClearingConsumerDeath⟩

/-- Applied local disposition.  Its only operational index is the exact C5
activation seed; all action and next facts remain generic compiler readouts. -/
structure SourceAppliedClearingBackstopAt
    (seed : partialBResidualConsumerCompiler.ExactActivationSeed) : Type where
  private mk ::
  seed_eq : seed = sourceGeneratedClearingBackstopExactSeed
  sourceCause : SourceClearingBackstopRestrictionAt seed

/-- Sole applied-disposition producer.  Its public mouth has no arguments. -/
def sourceGeneratedClearingBackstopDisposition :
    SourceAppliedClearingBackstopAt
      sourceGeneratedClearingBackstopExactSeed where
  seed_eq := rfl
  sourceCause := sourceClearingBackstopRestriction

/-! ## Exact local occurrence and action facts -/

@[simp] theorem sourceBackstop_occurrence_exact :
    sourceGeneratedClearingBackstopExactSeed.occurrence
        partialBResidualConsumerCompiler = partialOccurrence :=
  backstop_occurrence_exact

@[simp] theorem sourceBackstop_openSettlement_exact :
    sourceGeneratedClearingBackstopExactSeed.openSettlement
        partialBResidualConsumerCompiler = partialOpenB :=
  backstop_openSettlement_exact

@[simp] theorem sourceBackstop_event_exact :
    sourceGeneratedClearingBackstopExactSeed.activation
        partialBResidualConsumerCompiler =
      canonicalAClearingFace.counterpartyConsumer.event :=
  backstop_boundaryEvent_exact

@[simp] theorem sourceBackstop_edge_exact :
    sourceGeneratedClearingBackstopActivation.edge = fulfillB :=
  backstop_edge_exact

@[simp] theorem sourceBackstop_next_current_exact :
    sourceGeneratedClearingBackstopActivation.nextGeneratedState.current =
      fulfillB.target :=
  backstop_next_current_exact

@[simp] theorem sourceBackstop_whole_generated_next_exact :
    sourceGeneratedClearingBackstopActivation.nextGeneratedState.generated =
      .step (partialOccurrence.generatedState settlementCompiler).generated
        fulfillB :=
  backstop_whole_generated_next_exact

theorem sourceBackstop_history_exact :
    fulfillB.target.history =
      (partialOccurrence.current settlementCompiler).history ++
        [fulfillB.lifecycleEvent] :=
  backstop_history_exact

def sourceBackstopOwnership :
    SourceOwnsResponsibilityIncidence V
      (P.boundarySource
        canonicalAClearingFace.counterpartyConsumer.event)
      partialOpenB.obligation :=
  backstopSourceOwnership

def sourceBackstopFulfilledB :
    AutomaticFullFulfillment.FulfilledSlotAt (exchangeLaw := exchangeLaw)
      exactExchangeSeed
      sourceGeneratedClearingBackstopActivation.nextGeneratedState.current
      (.b : Leg) :=
  backstopFulfilledB

theorem sourceBackstop_exact_local_contract :
    sourceGeneratedClearingBackstopExactSeed.occurrence
          partialBResidualConsumerCompiler = partialOccurrence ∧
      sourceGeneratedClearingBackstopExactSeed.openSettlement
          partialBResidualConsumerCompiler = partialOpenB ∧
      sourceGeneratedClearingBackstopExactSeed.activation
          partialBResidualConsumerCompiler =
        canonicalAClearingFace.counterpartyConsumer.event ∧
      sourceGeneratedClearingBackstopActivation.edge = fulfillB ∧
      sourceGeneratedClearingBackstopActivation.nextGeneratedState.current =
        fulfillB.target ∧
      sourceGeneratedClearingBackstopActivation.nextGeneratedState.generated =
        .step (partialOccurrence.generatedState settlementCompiler).generated
          fulfillB ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          canonicalAClearingFace.counterpartyConsumer.event)
        partialOpenB.obligation) ∧
      Nonempty (AutomaticFullFulfillment.FulfilledSlotAt
        (exchangeLaw := exchangeLaw) exactExchangeSeed
        sourceGeneratedClearingBackstopActivation.nextGeneratedState.current
        (.b : Leg)) :=
  ⟨sourceBackstop_occurrence_exact,
    sourceBackstop_openSettlement_exact,
    sourceBackstop_event_exact,
    sourceBackstop_edge_exact,
    sourceBackstop_next_current_exact,
    sourceBackstop_whole_generated_next_exact,
    ⟨sourceBackstopOwnership⟩,
    ⟨sourceBackstopFulfilledB⟩⟩

/-! ## Root-polymorphic renewal law -/

abbrev ClearingBackstopConsumerAt
    (seed : partialBResidualConsumerCompiler.ExactActivationSeed) :=
  SourceClearingBackstopRestrictionAt seed

abbrev ClearingBackstopDispositionAt
    (seed : partialBResidualConsumerCompiler.ExactActivationSeed) :=
  SourceAppliedClearingBackstopAt seed

abbrev SourceClearingBackstopRenewalLawAt
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    (source : SourceNativeLedgerSource N RootV) :=
  SourceNativeRenewalProjectionLaw source LocalGame LocalSeed LocalSeedAt
    ClearingBackstopConsumerAt ClearingBackstopDispositionAt

/-- A later root supplies only its already generated renewal shell.  The
local seed, source restriction, and disposition remain fixed by C5. -/
def sourceClearingBackstopRenewalLaw
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (shell : SourceNativeRenewalRootShellAt source) :
    SourceClearingBackstopRenewalLawAt source :=
  SourceNativeRenewalProjectionLaw.ofRootShell shell
    sourceGeneratedClearingBackstopExactSeed
    sourceClearingBackstopRestriction
    sourceGeneratedClearingBackstopDisposition

@[simp] theorem sourceClearingBackstopRenewalLaw_compiles_exact_seed
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (shell : SourceNativeRenewalRootShellAt source)
    {current : RootV.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current)
    (active : (sourceClearingBackstopRenewalLaw shell).ActiveAt occurrence) :
    ((sourceClearingBackstopRenewalLaw shell).compile occurrence active).sourceSeed =
      sourceGeneratedClearingBackstopExactSeed :=
  rfl

@[simp] theorem sourceClearingBackstopRenewalLaw_compiles_exact_consumer
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (shell : SourceNativeRenewalRootShellAt source)
    {current : RootV.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current)
    (active : (sourceClearingBackstopRenewalLaw shell).ActiveAt occurrence) :
    ((sourceClearingBackstopRenewalLaw shell).compile occurrence active).consumer =
      sourceClearingBackstopRestriction :=
  rfl

@[simp] theorem sourceClearingBackstopRenewalLaw_compiles_exact_disposition
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (shell : SourceNativeRenewalRootShellAt source)
    {current : RootV.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current)
    (active : (sourceClearingBackstopRenewalLaw shell).ActiveAt occurrence) :
    ((sourceClearingBackstopRenewalLaw shell).compile occurrence active).disposition =
      sourceGeneratedClearingBackstopDisposition :=
  rfl

/-! ## Exact no-forgery controls -/

theorem noBackstopCause_noDisposition
    (noCause : IsEmpty (SourceClearingBackstopRestrictionAt
      sourceGeneratedClearingBackstopExactSeed)) :
    IsEmpty (SourceAppliedClearingBackstopAt
      sourceGeneratedClearingBackstopExactSeed) :=
  ⟨fun disposition => noCause.false disposition.sourceCause⟩

theorem oldCompiler_controls_remain_exact :
    (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
        (activation.openSettlement residualConsumerCompiler).leg = .b) ∧
      (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
        activation.occurrence residualConsumerCompiler = partialOccurrence) :=
  oldResidualCompiler_still_cannot_source_backstop

theorem backstop_disposition_mouth_has_no_action_root_or_future_fields : True := by
  let disposition := sourceGeneratedClearingBackstopDisposition
  fail_if_success exact disposition.adapter
  fail_if_success exact disposition.activation
  fail_if_success exact disposition.edge
  fail_if_success exact disposition.next
  fail_if_success exact disposition.root
  fail_if_success exact disposition.selectedRow
  fail_if_success exact disposition.ledger
  fail_if_success exact disposition.coverage
  fail_if_success exact disposition.run
  fail_if_success exact disposition.registry
  fail_if_success exact disposition.completedFuture
  trivial

end
end M14SourceClearingBackstopRenewal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopRenewal.sourceClearingBackstopRestriction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopRenewal.sourceGeneratedClearingBackstopDisposition
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopRenewal.sourceBackstop_exact_local_contract
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopRenewal.sourceClearingBackstopRenewalLaw
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopRenewal.sourceClearingBackstopRenewalLaw_compiles_exact_seed
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceClearingBackstopRenewal.oldCompiler_controls_remain_exact
