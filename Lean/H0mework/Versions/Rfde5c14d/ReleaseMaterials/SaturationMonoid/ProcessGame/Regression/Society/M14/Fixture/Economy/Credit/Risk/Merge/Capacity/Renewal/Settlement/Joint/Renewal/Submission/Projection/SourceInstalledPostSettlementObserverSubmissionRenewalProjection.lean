import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Bootstrap.SourceGeneratedPostSettlementObserverSubmissionBootstrap
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8RevisedWorld
import H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection

/-!
# Pre-emitter observer-submission augmentation of the richer M9 revision

The existing visit-polymorphic loss-allocation source keeps its network,
vocabulary, ledger compiler, split coverage, inquiry faces and emitter.
The observer submission is installed as one additional dependent renewal face
of that source's first generated row.  It does not generate or rename the
obstruction row and does not alter loss-allocation semantics.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverSubmissionU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UniversalRootGrammar
open M9ProofCarryingRenewalInquiryRoot
open M14SourceGeneratedContributionMergeActionSource

abbrev AugmentedNewNAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8RevisedWorld.NewNAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

abbrev AugmentedNewVAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8RevisedWorld.NewVAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

/-! Compatibility mouths consumed by the already separated execution and
runtime modules.  They now denote the richer augmented carrier. -/
abbrev NewNAt := AugmentedNewNAt
abbrev NewVAt := AugmentedNewVAt

def newRevisedEntryAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8RevisedLedger.newRevisedEntryAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def revisedLedgerSourceAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeLedgerSource (NewNAt oldVisit sourceIndex boundary)
      (NewVAt oldVisit sourceIndex boundary) :=
  M9ProofCarryingRenewalU8RevisedLedger.revisedLedgerSourceAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def augmentedBaseAuthoritySourceAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeAuthoritySource
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedAuthoritySourceAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

/-- The existing richer revision's first row is selected by its own compiler.
The shell adds no material and cannot change that row or successor. -/
def augmentedSubmissionRootShellAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeRenewalRootShellAt
      (augmentedBaseAuthoritySourceAt oldVisit sourceIndex boundary
        ).restructuringSource.toLedgerSource where
  ActiveAt := fun {current} _occurrence => PLift (current = (0 : Nat))
  InactiveAt := fun {current} _occurrence => PLift (current ≠ (0 : Nat))
  classify := by
    intro current occurrence
    by_cases current_eq : current = (0 : Nat)
    · exact .inl ⟨current_eq⟩
    · exact .inr ⟨current_eq⟩
  sourceEntry := by
    intro current occurrence active
    cases active.down
    have occurrence_eq :=
      M13ReflexiveClaimLifecycleFixture.revisedOccurrence_eq_emitted_at
        (oldRootVisitAt oldVisit sourceIndex boundary) occurrence
    cases occurrence_eq
    exact M9ProofCarryingRenewalU8RevisedLedger.newRevisedEntryAt
      (oldRootVisitAt oldVisit sourceIndex boundary)
  selectedRow := by
    intro current occurrence active
    cases active.down
    have occurrence_eq :=
      M13ReflexiveClaimLifecycleFixture.revisedOccurrence_eq_emitted_at
        (oldRootVisitAt oldVisit sourceIndex boundary) occurrence
    cases occurrence_eq
    exact
      (M9ProofCarryingRenewalU8RevisedWorld.revisedNewEntryRowAt
        (oldRootVisitAt oldVisit sourceIndex boundary)).sourceRow
  successor := by
    intro current occurrence active
    cases active.down
    have occurrence_eq :=
      M13ReflexiveClaimLifecycleFixture.revisedOccurrence_eq_emitted_at
        (oldRootVisitAt oldVisit sourceIndex boundary) occurrence
    cases occurrence_eq
    exact M9ProofCarryingRenewalU8RevisedWorld.revisedFirstSuccessorAt
      (oldRootVisitAt oldVisit sourceIndex boundary)
  activeOccurrences_eq := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence
      leftActive rightActive
    cases leftActive.down
    cases rightActive.down
    have left_eq :=
      M13ReflexiveClaimLifecycleFixture.revisedOccurrence_eq_emitted_at
        (oldRootVisitAt oldVisit sourceIndex boundary) leftOccurrence
    have right_eq :=
      M13ReflexiveClaimLifecycleFixture.revisedOccurrence_eq_emitted_at
        (oldRootVisitAt oldVisit sourceIndex boundary) rightOccurrence
    cases left_eq
    cases right_eq
    rfl

def augmentedSubmissionRenewalLawAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeRenewalProjectionLaw
      (augmentedBaseAuthoritySourceAt oldVisit sourceIndex boundary
        ).restructuringSource.toLedgerSource
      (localGame oldVisit sourceIndex boundary) LocalSeed
      (LocalSeedAt oldVisit sourceIndex boundary)
      (LocalConsumerAt oldVisit sourceIndex boundary)
      (LocalDispositionAt oldVisit sourceIndex boundary) :=
  SourceNativeRenewalProjectionLaw.ofRootShell
    (augmentedSubmissionRootShellAt oldVisit sourceIndex boundary)
    (localSourceSeed oldVisit sourceIndex boundary)
    (localConsumer oldVisit sourceIndex boundary)
    (localDisposition oldVisit sourceIndex boundary)

/-- This source exists before either augmented root emitter is constructed. -/
def augmentedAuthoritySourceAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeAuthoritySource
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) :=
  withRenewalProjection
    (augmentedBaseAuthoritySourceAt oldVisit sourceIndex boundary)
    (augmentedSubmissionRenewalLawAt oldVisit sourceIndex boundary)

def augmentedSubmissionInstallationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  renewalComponent
    (augmentedBaseAuthoritySourceAt oldVisit sourceIndex boundary)
    (augmentedSubmissionRenewalLawAt oldVisit sourceIndex boundary)

theorem augmentedSource_preservesExistingRestructuring
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (augmentedAuthoritySourceAt oldVisit sourceIndex boundary
      ).restructuringSource =
      (augmentedBaseAuthoritySourceAt oldVisit sourceIndex boundary
        ).restructuringSource :=
  rfl

end
end M14SourceGeneratedPostSettlementObserverSubmissionU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.augmentedSubmissionRenewalLawAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.augmentedSource_preservesExistingRestructuring
