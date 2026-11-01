import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Installation.Execution.SourceGeneratedCycleMemoryPlatformGateU8Compilation

/-!
# Causal row authority of the platform-gate revised root

The revised root is followed through its literal generated successors.  The
row lineage is the existing loss-allocation lineage; the platform-gate face
does not select entries or manufacture a temporal history.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCycleMemoryPlatformGateU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8

abbrev platformGateRevisedU7At (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedU7At
    (oldRootVisitAt oldVisit sourceIndex boundary)

abbrev platformGateRevisedCalculusAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedCalculusAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

abbrev platformGateRevisedTheoryAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedTheoryAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def platformGateRevisedVisitAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    Nat → RootVisit
      (platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot
  | 0 =>
      (platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot.initialVisit
  | index + 1 =>
      (platformGateRevisedVisitAt oldVisit sourceIndex boundary index).next rfl

def platformGateRevisedTemporalVisitAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    SourceNativeTemporalVisitAt
      (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite
    (platformGateRevisedVisitAt oldVisit sourceIndex boundary index)

def platformGateRevisedInquiryEventAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :=
  ULift.up.{1, 0}
    ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary).emitted
      (platformGateRevisedVisitAt oldVisit sourceIndex boundary index).current)

def platformGateRevisedInquiryEntryAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    OpenResponsibilityAt
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
            ).emitted
            (platformGateRevisedVisitAt oldVisit sourceIndex boundary index
              ).current)) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedInquiryEntryAtVisit
    (oldRootVisitAt oldVisit sourceIndex boundary)
    (platformGateRevisedVisitAt oldVisit sourceIndex boundary index).current

theorem platformGateRevisedNextEqAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
      ).toAuthoritativeRoot.toRoot.evolutionAt
        (platformGateRevisedVisitAt oldVisit sourceIndex boundary index).current
      ).nextCurrent? =
      some
        (platformGateRevisedVisitAt oldVisit sourceIndex boundary (index + 1)
          ).current :=
  rfl

theorem platformGateRevisedTemporalVisit_next_eq (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    (platformGateRevisedTemporalVisitAt oldVisit sourceIndex boundary index
      ).next (platformGateRevisedNextEqAt oldVisit sourceIndex boundary index) =
      platformGateRevisedTemporalVisitAt oldVisit sourceIndex boundary
        (index + 1) :=
  rfl

theorem platformGateRevisedLivingRoot_generatedNextCurrentAt_eq
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
      ).generatedNextCurrentAt
        (platformGateRevisedTemporalVisitAt oldVisit sourceIndex boundary
          index) =
      ⟨AugmentedNewVAt oldVisit sourceIndex boundary,
        platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary,
        platformGateRevisedTemporalVisitAt oldVisit sourceIndex boundary
          (index + 1)⟩ := by
  cases index <;> rfl

def platformGateRevisedVisitEntryAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    (index : Nat) →
      OpenResponsibilityAt
        (AugmentedNewNAt oldVisit sourceIndex boundary)
        ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
          ).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
            ((platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
              ).emitted
              (platformGateRevisedVisitAt oldVisit sourceIndex boundary index
                ).current))
  | 0 =>
      M9ProofCarryingRenewalU8RevisedLedger.newRevisedEntryAt
        (oldRootVisitAt oldVisit sourceIndex boundary)
  | index + 1 =>
      (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
          (platformGateRevisedNextEqAt oldVisit sourceIndex boundary index)
          (platformGateRevisedVisitEntryAt oldVisit sourceIndex boundary index)

theorem platformGateRevisedVisitEntry_eq_inquiryEntry
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    platformGateRevisedVisitEntryAt oldVisit sourceIndex boundary index =
      platformGateRevisedInquiryEntryAt oldVisit sourceIndex boundary index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
          ).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
            (platformGateRevisedNextEqAt oldVisit sourceIndex boundary index)
            (platformGateRevisedVisitEntryAt oldVisit sourceIndex boundary
              index) =
          platformGateRevisedInquiryEntryAt oldVisit sourceIndex boundary
            (index + 1)
      rw [inductionHypothesis]
      cases index <;> rfl

def platformGateRevisedInitialAuthorityAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary)
      (platformGateRevisedTemporalVisitAt oldVisit sourceIndex boundary 0)
      (platformGateRevisedVisitEntryAt oldVisit sourceIndex boundary 0) :=
  ((SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial?
    (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary)
    (platformGateRevisedVisitEntryAt oldVisit sourceIndex boundary 0)
    .initial).get (by rfl)).2

def platformGateRevisedAuthorityAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    (index : Nat) →
      SourceNativeLivingTemporalCausalEntryAuthorityAt
        (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary)
        (platformGateRevisedTemporalVisitAt oldVisit sourceIndex boundary
          index)
        (platformGateRevisedVisitEntryAt oldVisit sourceIndex boundary index)
  | 0 => platformGateRevisedInitialAuthorityAt oldVisit sourceIndex boundary
  | index + 1 =>
      (platformGateRevisedAuthorityAt oldVisit sourceIndex boundary index).next
        (platformGateRevisedNextEqAt oldVisit sourceIndex boundary index)

abbrev platformGateRevisedInquiryAuthorityAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary)
      (platformGateRevisedTemporalVisitAt oldVisit sourceIndex boundary index)
      (platformGateRevisedInquiryEntryAt oldVisit sourceIndex boundary index) := by
  rw [← platformGateRevisedVisitEntry_eq_inquiryEntry oldVisit sourceIndex
    boundary index]
  exact platformGateRevisedAuthorityAt oldVisit sourceIndex boundary index

@[simp] theorem platformGateRevisedVisit_current_exact (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    (show Nat from
      (platformGateRevisedVisitAt oldVisit sourceIndex boundary index
        ).current) = index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        (show Nat from
          (platformGateRevisedVisitAt oldVisit sourceIndex boundary index
            ).current) + 1 = index + 1
      rw [inductionHypothesis]

end
end M14SourceGeneratedCycleMemoryPlatformGateU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateRevisedVisitEntry_eq_inquiryEntry
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateRevisedInquiryAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateRevisedLivingRoot_generatedNextCurrentAt_eq
