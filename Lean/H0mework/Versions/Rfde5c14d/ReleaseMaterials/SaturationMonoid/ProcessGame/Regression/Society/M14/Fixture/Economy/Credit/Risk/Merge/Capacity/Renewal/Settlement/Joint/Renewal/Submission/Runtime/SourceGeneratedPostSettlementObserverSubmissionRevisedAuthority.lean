import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Execution.SourceGeneratedPostSettlementObserverSubmissionU8Compilation

/-!
# Causal row authority of the observer-submission revised root

The richer revision's current-indexed inquiry row is followed through the
revised root's literal generated successors.  Inquiry states consume this
single authority lineage;
they do not reselect an entry or construct another temporal history.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverSubmissionU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource

abbrev revisedU7At (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedU7At
    (oldRootVisitAt oldVisit sourceIndex boundary)

abbrev revisedCalculusAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedCalculusAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

abbrev revisedTheoryAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedTheoryAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def revisedVisitAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nat → RootVisit
      (revisedAuthoritativeRootAt oldVisit sourceIndex boundary).toRoot
  | 0 =>
      (revisedAuthoritativeRootAt oldVisit sourceIndex boundary).toRoot.initialVisit
  | index + 1 => (revisedVisitAt oldVisit sourceIndex boundary index).next rfl

def revisedTemporalVisitAt (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeTemporalVisitAt
      (revisedLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (revisedVisitAt oldVisit sourceIndex boundary index)

def revisedInquiryEventAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :=
  ULift.up.{1, 0}
    ((revisedLivingRootAt oldVisit sourceIndex boundary).emitted
      (revisedVisitAt oldVisit sourceIndex boundary index).current)

def revisedInquiryEntryAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    OpenResponsibilityAt (NewNAt oldVisit sourceIndex boundary)
      ((revisedLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          ((revisedLivingRootAt oldVisit sourceIndex boundary).emitted
            (revisedVisitAt oldVisit sourceIndex boundary index).current)) :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedInquiryEntryAtVisit
    (oldRootVisitAt oldVisit sourceIndex boundary)
    (revisedVisitAt oldVisit sourceIndex boundary index).current

theorem revisedNextEqAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    ((revisedLivingRootAt oldVisit sourceIndex boundary
      ).toAuthoritativeRoot.toRoot.evolutionAt
        (revisedVisitAt oldVisit sourceIndex boundary index).current
      ).nextCurrent? =
      some (revisedVisitAt oldVisit sourceIndex boundary (index + 1)).current :=
  rfl

theorem revisedTemporalVisit_next_eq (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    (revisedTemporalVisitAt oldVisit sourceIndex boundary index).next
        (revisedNextEqAt oldVisit sourceIndex boundary index) =
      revisedTemporalVisitAt oldVisit sourceIndex boundary (index + 1) :=
  rfl

theorem revisedLivingRoot_generatedNextCurrentAt_eq (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    (revisedLivingRootAt oldVisit sourceIndex boundary).generatedNextCurrentAt
        (revisedTemporalVisitAt oldVisit sourceIndex boundary index) =
      ⟨NewVAt oldVisit sourceIndex boundary,
        revisedAuthoritativeRootAt oldVisit sourceIndex boundary,
        revisedTemporalVisitAt oldVisit sourceIndex boundary (index + 1)⟩ := by
  cases index <;> rfl

def revisedVisitEntryAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    (index : Nat) →
      OpenResponsibilityAt (NewNAt oldVisit sourceIndex boundary)
        ((revisedLivingRootAt oldVisit sourceIndex boundary
          ).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
            ((revisedLivingRootAt oldVisit sourceIndex boundary).emitted
              (revisedVisitAt oldVisit sourceIndex boundary index).current))
  | 0 => newRevisedEntryAt oldVisit sourceIndex boundary
  | index + 1 =>
      (revisedLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
          (revisedNextEqAt oldVisit sourceIndex boundary index)
          (revisedVisitEntryAt oldVisit sourceIndex boundary index)

theorem revisedVisitEntry_eq_inquiryEntry (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    revisedVisitEntryAt oldVisit sourceIndex boundary index =
      revisedInquiryEntryAt oldVisit sourceIndex boundary index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        (revisedLivingRootAt oldVisit sourceIndex boundary
          ).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
            (revisedNextEqAt oldVisit sourceIndex boundary index)
            (revisedVisitEntryAt oldVisit sourceIndex boundary index) =
          revisedInquiryEntryAt oldVisit sourceIndex boundary (index + 1)
      rw [inductionHypothesis]
      cases index <;> rfl

def revisedInitialAuthorityAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (revisedLivingRootAt oldVisit sourceIndex boundary)
      (revisedTemporalVisitAt oldVisit sourceIndex boundary 0)
      (revisedVisitEntryAt oldVisit sourceIndex boundary 0) :=
  ((SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial?
    (revisedLivingRootAt oldVisit sourceIndex boundary)
    (revisedVisitEntryAt oldVisit sourceIndex boundary 0) .initial).get
      (by rfl)).2

def revisedAuthorityAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (index : Nat) →
      SourceNativeLivingTemporalCausalEntryAuthorityAt
        (revisedLivingRootAt oldVisit sourceIndex boundary)
        (revisedTemporalVisitAt oldVisit sourceIndex boundary index)
        (revisedVisitEntryAt oldVisit sourceIndex boundary index)
  | 0 => revisedInitialAuthorityAt oldVisit sourceIndex boundary
  | index + 1 =>
      (revisedAuthorityAt oldVisit sourceIndex boundary index).next
        (revisedNextEqAt oldVisit sourceIndex boundary index)

abbrev revisedInquiryAuthorityAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (revisedLivingRootAt oldVisit sourceIndex boundary)
      (revisedTemporalVisitAt oldVisit sourceIndex boundary index)
      (revisedInquiryEntryAt oldVisit sourceIndex boundary index) := by
  rw [← revisedVisitEntry_eq_inquiryEntry oldVisit sourceIndex boundary index]
  exact revisedAuthorityAt oldVisit sourceIndex boundary index

@[simp] theorem revisedVisit_current_exact (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    (show Nat from
      (revisedVisitAt oldVisit sourceIndex boundary index).current) = index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        (show Nat from
          (revisedVisitAt oldVisit sourceIndex boundary index).current) + 1 =
            index + 1
      rw [inductionHypothesis]

end
end M14SourceGeneratedPostSettlementObserverSubmissionU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.revisedVisitEntry_eq_inquiryEntry
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.revisedInquiryAuthorityAt
