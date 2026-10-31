import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Transport.SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Projection.SourceInstalledPostSettlementObserverSubmissionRenewalProjection

/-!
# Pre-emitter installation of the cycle-memory platform gate

The existing observer-submission U8 source is augmented by one further
dependent renewal face on its already generated new-only first row.  The face
consumes the cofinal platform cycle-memory obstruction and exposes the revised
channel candidate.  Network, vocabulary, restructuring compiler, ledger rows
and successor are unchanged.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCycleMemoryPlatformGateU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal
open M14EssentialAccessRelationFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedActualRelationThreeCycle
open M14SourceGeneratedCycleMemoryPlatformGateObstruction
open M14SourceGeneratedPlatformChannelRevisionCandidate
open M14SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport

abbrev PlatformGateSeed :=
  essentialAccessRelationCompiler.ExactRelationSeed

abbrev LocalSource := M14SourceGeneratedPostSettlementObserverSubmissionU8.LocalSource

abbrev LocalState (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M14SourceGeneratedPostSettlementObserverSubmissionU8.LocalState oldVisit
    sourceIndex boundary

def PlatformGateSeedAt (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (_source : LocalSource)
    (state : LocalState oldVisit sourceIndex boundary)
    (seed : PlatformGateSeed) : Prop :=
  seed = actualRelationSeedAt (platformCycleBaseAfter boundary) ∧
    state.scenario = .actual ∧ state.face = .ledger

def platformGateLocalSourceSeed (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceSeed
      (localOccurrenceOf oldVisit sourceIndex boundary)
      PlatformGateSeed
      (PlatformGateSeedAt oldVisit sourceIndex boundary)
      (localGame oldVisit sourceIndex boundary).source := by
  refine ⟨actualRelationSeedAt (platformCycleBaseAfter boundary), ?_⟩
  let occurrence := localOccurrenceOf oldVisit sourceIndex boundary
    (localGame oldVisit sourceIndex boundary).source
  exact ⟨occurrence.root, occurrence.root_mem_trace, rfl, rfl, rfl⟩

abbrev PlatformGateConsumerAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (_seed : SourceSeed
      (localOccurrenceOf oldVisit sourceIndex boundary)
      PlatformGateSeed
      (PlatformGateSeedAt oldVisit sourceIndex boundary)
      (localGame oldVisit sourceIndex boundary).source) :=
  PLift (Nonempty
    (SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
      oldVisit sourceIndex boundary))

abbrev PlatformGateDispositionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (_seed : SourceSeed
      (localOccurrenceOf oldVisit sourceIndex boundary)
      PlatformGateSeed
      (PlatformGateSeedAt oldVisit sourceIndex boundary)
      (localGame oldVisit sourceIndex boundary).source) :=
  PLift (Nonempty
    (SourceGeneratedPlatformChannelRevisionCandidateAt boundary))

def platformGateConsumer (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    PlatformGateConsumerAt oldVisit sourceIndex boundary
      (platformGateLocalSourceSeed oldVisit sourceIndex boundary) :=
  ⟨⟨sourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
    oldVisit sourceIndex boundary⟩⟩

def platformGateDisposition (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    PlatformGateDispositionAt oldVisit sourceIndex boundary
      (platformGateLocalSourceSeed oldVisit sourceIndex boundary) :=
  ⟨⟨sourceGeneratedPlatformChannelRevisionCandidateAt boundary⟩⟩

/-- The existing first row is selected by its existing compiler.  This shell
adds no row, target or successor. -/
def platformGateRootShellAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeRenewalRootShellAt
      (augmentedAuthoritySourceAt oldVisit sourceIndex boundary
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

def platformGateRenewalLawAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeRenewalProjectionLaw
      (augmentedAuthoritySourceAt oldVisit sourceIndex boundary
        ).restructuringSource.toLedgerSource
      (localGame oldVisit sourceIndex boundary)
      PlatformGateSeed
      (PlatformGateSeedAt oldVisit sourceIndex boundary)
      (PlatformGateConsumerAt oldVisit sourceIndex boundary)
      (PlatformGateDispositionAt oldVisit sourceIndex boundary) :=
  SourceNativeRenewalProjectionLaw.ofRootShell
    (platformGateRootShellAt oldVisit sourceIndex boundary)
    (platformGateLocalSourceSeed oldVisit sourceIndex boundary)
    (platformGateConsumer oldVisit sourceIndex boundary)
    (platformGateDisposition oldVisit sourceIndex boundary)

/-- Double augmentation: keep the installed observer-submission face and add
the source-generated platform-gate face before emission. -/
def platformGateAuthoritySourceAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeAuthoritySource
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) :=
  withRenewalProjection
    (augmentedAuthoritySourceAt oldVisit sourceIndex boundary)
    (platformGateRenewalLawAt oldVisit sourceIndex boundary)

def platformGateInstallationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  renewalComponent
    (augmentedAuthoritySourceAt oldVisit sourceIndex boundary)
    (platformGateRenewalLawAt oldVisit sourceIndex boundary)

theorem platformGateSource_preservesExistingRestructuring
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (platformGateAuthoritySourceAt oldVisit sourceIndex boundary
      ).restructuringSource =
      (augmentedAuthoritySourceAt oldVisit sourceIndex boundary
        ).restructuringSource :=
  rfl

end
end M14SourceGeneratedCycleMemoryPlatformGateU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateLocalSourceSeed
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateRenewalLawAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateSource_preservesExistingRestructuring
