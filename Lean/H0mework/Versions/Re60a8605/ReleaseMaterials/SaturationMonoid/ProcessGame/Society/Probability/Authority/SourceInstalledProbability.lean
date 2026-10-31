import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Consumer.ObserverConditionedPrediction
import H0mework.Society.Renewal.InstalledRenewalProjection

/-!
# Source-installed observer probability

Observer-conditioned probability receives root authority only as a dependent
restriction of an M8 renewal law installed before the root emitter.  The
restriction is indexed by the exact normalized fold, conditioning visible and
zero-field prediction consumer.  Its sole stored datum is the proof that the
renewal payload seed is the fixed focal source seed.

Probability values, prediction classifications, finite supports, scaling
data, root successors and completed decisions are never payload fields.  All
numeric information remains a derived readout, while responsibility,
whole-ledger write-back and the next current come from the existing installed
root occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Probability
namespace Authority

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Capacity Space Observer
open Measure Kernel Consumer

universe u

variable {Source State Seed : Type u}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {SeedAt : Source → State → Seed → Prop}
variable {Lineage : Source → Type u}
variable {lineageOf : ∀ source,
  SourceSeed occurrenceOf Seed SeedAt source → Lineage source}
variable {focal : SourceSeed occurrenceOf Seed SeedAt game.source}
variable {rateCompiler : SourceOwnedOccurrenceRateCompiler.{u, u, u, u, u}
  game Seed SeedAt Lineage lineageOf focal}
variable {crossingCompiler : SourceOwnedCrossingCompiler.{u, u, u, u, u,
  u, u, u, u, u, u} rateCompiler}
variable {socialSpace : SourceGeneratedSocialSpaceAt crossingCompiler}
variable {measureCompiler : SourceOwnedFiniteMeasureCompilerAt socialSpace}
variable {sourceMeasure : SourceGeneratedFiniteMeasureAt measureCompiler}

variable {Visible AuthorityResidual : Type u}
variable {observer : AuthorityObserver crossingCompiler.ExactCrossing Visible
  AuthorityResidual}
variable {event : crossingCompiler.ExactCrossing → Prop}

noncomputable section

/-! ## Pre-emitter exact restriction -/

/-- Proof-only payload restriction indexed by the exact normalized fold,
conditioned visible and derived prediction consumer. -/
structure ProbabilityRestrictionAt
    (fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event)
    (visible : Visible)
    (prediction : SourceGeneratedObserverConditionedPredictionAt fold visible)
    (seed : SourceSeed occurrenceOf Seed SeedAt game.source) : Type u where
  seed_eq_focal : seed = focal

/-- Fixed local consumer family installed in the M8 projection law. -/
abbrev ProbabilityRestrictionConsumerAt
    (fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event)
    (visible : Visible)
    (prediction : SourceGeneratedObserverConditionedPredictionAt fold visible)
    (seed : SourceSeed occurrenceOf Seed SeedAt game.source) : Type u :=
  ProbabilityRestrictionAt fold visible prediction seed

/-- M8 recognition whose local consumer is definitionally the indexed
probability restriction. -/
abbrev SourceNativeProbabilityRecognitionAt
    {N : WorldRelationNetwork.{u}}
    {RootV : ConstructiveRoot.Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N RootV)
    (fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event)
    (visible : Visible)
    (prediction : SourceGeneratedObserverConditionedPredictionAt fold visible)
    (DispositionAt :
      SourceSeed occurrenceOf Seed SeedAt game.source → Type u) :=
  SourceNativeRenewalRecognitionAt root game Seed SeedAt
    (ProbabilityRestrictionConsumerAt fold visible prediction) DispositionAt

variable {fold : SourceGeneratedObserverKernelFoldAt
  sourceMeasure observer event}
variable {visible : Visible}
variable {prediction :
  SourceGeneratedObserverConditionedPredictionAt fold visible}

variable {N : WorldRelationNetwork.{u}}
variable {RootV : ConstructiveRoot.Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N RootV}
variable {DispositionAt :
  SourceSeed occurrenceOf Seed SeedAt game.source → Type u}
variable {recognition : SourceNativeProbabilityRecognitionAt
  root fold visible prediction DispositionAt}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}
variable {installed : SourceInstalledRenewalAt recognition visit}

/-! ## Installed probability authority -/

/-- Zero-field seal over the exact source-installed renewal. -/
structure SourceInstalledProbabilityAt
    (installed : SourceInstalledRenewalAt recognition visit) : Type (u + 2) where
  private mk ::

/-- Sole installed-probability producer.  It accepts no probability value,
classification, support, successor or completed outcome. -/
def sourceInstalledProbability
    (installed : SourceInstalledRenewalAt recognition visit) :
    SourceInstalledProbabilityAt installed :=
  ⟨⟩

namespace SourceInstalledProbabilityAt

variable (installedProbability : SourceInstalledProbabilityAt installed)

/-- Proof-only restriction read from the pre-emitter payload. -/
def restriction : ProbabilityRestrictionAt fold visible prediction
    installed.payload.sourceSeed := by
  cases installedProbability
  exact installed.payload.consumer

@[simp] theorem renewalSeed_eq_focal
    (installedProbability : SourceInstalledProbabilityAt installed) :
    installed.payload.sourceSeed = focal :=
  ProbabilityRestrictionAt.seed_eq_focal installedProbability.restriction

/-- Exact normalized fold retained by the restriction index. -/
def normalizedFold : SourceGeneratedObserverKernelFoldAt
    sourceMeasure observer event := by
  cases installedProbability
  exact fold

/-- Exact source-generated finite measure retained through the fold index. -/
def sourceMeasureSeal : SourceGeneratedFiniteMeasureAt measureCompiler := by
  cases installedProbability
  exact sourceMeasure

/-- Existing observer retained through the fold index. -/
def authorityObserver : AuthorityObserver crossingCompiler.ExactCrossing
    Visible AuthorityResidual := by
  cases installedProbability
  exact observer

/-- Event predicate retained through the fold index. -/
def eventPredicate : crossingCompiler.ExactCrossing → Prop := by
  cases installedProbability
  exact event

/-- Exact conditioning visible retained by the restriction index. -/
def conditionedVisible : Visible := by
  cases installedProbability
  exact visible

/-- Exact zero-field prediction consumer retained by the restriction index. -/
def predictionConsumer :
    SourceGeneratedObserverConditionedPredictionAt
      installedProbability.normalizedFold
      installedProbability.conditionedVisible := by
  cases installedProbability
  exact prediction

section ComputableReadouts

variable [DecidableEq Visible]
variable [DecidablePred event]

/-- Derived normalized readout; it is never stored in the payload. -/
def normalizedProbability : Option ℚ≥0 :=
  installedProbability.predictionConsumer.probability

/-- Derived prediction classification; it is never stored in the payload. -/
def predictionClassification :
    Option ObserverConditionedPredictionClass :=
  installedProbability.predictionConsumer.classification

/-- Existing visibly factorized probability readout. -/
def probabilityReadout :
    OccurrenceReadout crossingCompiler.ExactCrossing (Option ℚ≥0) :=
  installedProbability.predictionConsumer.probabilityReadout

/-- Existing factorization through the indexed observer. -/
def exactReadoutFactorization :
    ReadoutFactorization observer installedProbability.probabilityReadout :=
  installedProbability.predictionConsumer.exactReadoutFactorization

/-- Installation does not upgrade the visible probability to hidden-authority
reconstruction. -/
theorem noAuthorityCompleteProbability
    (pair : AuthorityKernelPair observer) :
    ¬ Nonempty (AuthorityCompleteReadoutAt observer
      installedProbability.probabilityReadout) :=
  installedProbability.predictionConsumer.noAuthorityCompleteConsumer pair

end ComputableReadouts

/-- Independent M8 responsibility consumer at the same exact root row. -/
def rootConsumer :
    RenewalResponsibilityConsumerAt installed.operationalAuthority := by
  cases installedProbability
  exact installed.rootResponsibilityConsumer

/-- Whole-ledger write-back at the installed probability occurrence. -/
def wholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      root.toAuthoritativeRoot.toLedgerRoot.source.source
      (root.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit visit).occurrence := by
  cases installedProbability
  exact (root.toAuthoritativeRoot.toLedgerRoot
    |>.generatedAtTemporalVisit visit).wholeLedgerWriteBack

/-- Existing root-generated next.  Probability installation emits no local
successor or probability scheduler. -/
def generatedNext : SourceNativeAuthoritativeRootCurrentAt N := by
  cases installedProbability
  exact root.generatedNextCurrentAt visit

theorem rootAnswerAndNext_factorizes
    (installedProbability : SourceInstalledProbabilityAt installed) :
    installed.RootAnswerAndNextFactorizes := by
  cases installedProbability
  exact installed.rootAnswerAndNext_factorizes

end SourceInstalledProbabilityAt

/-! ## Independent root consumer -/

/-- Independent consumer of the exact installed restriction and existing root
answer-and-next.  It deliberately has no probability or classification field. -/
structure SourceInstalledProbabilityConsumerAt
    (installedProbability : SourceInstalledProbabilityAt installed) :
    Type (u + 4) where
  private mk ::
  restriction : ProbabilityRestrictionAt fold visible prediction
    installed.payload.sourceSeed
  restriction_eq : restriction = installedProbability.restriction
  normalizedFold : SourceGeneratedObserverKernelFoldAt
    sourceMeasure observer event
  normalizedFold_eq : normalizedFold = installedProbability.normalizedFold
  conditionedVisible : Visible
  conditionedVisible_eq :
    conditionedVisible = installedProbability.conditionedVisible
  predictionConsumer :
    SourceGeneratedObserverConditionedPredictionAt
      normalizedFold conditionedVisible
  predictionConsumer_heq : HEq predictionConsumer
    installedProbability.predictionConsumer
  rootConsumer : RenewalResponsibilityConsumerAt installed.operationalAuthority
  wholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      root.toAuthoritativeRoot.toLedgerRoot.source.source
      (root.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit visit).occurrence
  generatedNext : SourceNativeAuthoritativeRootCurrentAt N
  generatedNext_eq : generatedNext = root.generatedNextCurrentAt visit
  rootFactorization : installed.RootAnswerAndNextFactorizes

/-- Sole independent consumer producer. -/
def SourceInstalledProbabilityAt.independentConsumer
    (installedProbability : SourceInstalledProbabilityAt installed) :
    SourceInstalledProbabilityConsumerAt installedProbability where
  restriction := installedProbability.restriction
  restriction_eq := rfl
  normalizedFold := installedProbability.normalizedFold
  normalizedFold_eq := rfl
  conditionedVisible := installedProbability.conditionedVisible
  conditionedVisible_eq := rfl
  predictionConsumer := installedProbability.predictionConsumer
  predictionConsumer_heq := HEq.rfl
  rootConsumer := installedProbability.rootConsumer
  wholeLedgerWriteBack := installedProbability.wholeLedgerWriteBack
  generatedNext := installedProbability.generatedNext
  generatedNext_eq := rfl
  rootFactorization := installedProbability.rootAnswerAndNext_factorizes

end
end Authority
end Probability
end Society
end ProcessGame
end SaturationMonoid
