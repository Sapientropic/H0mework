import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Root.SourceGeneratedContributionCapacityReopeningRoot

/-!
# Exact source coordinate of capacity reopening

The action starts from the generated residual row of the capacity-U8 revised
root.  Its source index determines the periodic UBI occurrence; no payment,
exit witness, target root or future is accepted from the caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityReopeningActionSource

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRoot

def contributionCapacityReopeningActionSourceRootAt
    (oldVisit : OldVisit) := CapacityU8RootAt oldVisit

def contributionCapacityReopeningActionSourceVisitAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacityU8RuntimeVisitAt oldVisit sourceIndex

def contributionCapacityReopeningActionSourceEntryAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    OpenResponsibilityAt (CapacityU8NAt oldVisit)
      ((contributionCapacityReopeningActionSourceRootAt oldVisit)
        |>.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          ((contributionCapacityReopeningActionSourceRootAt oldVisit).emitted
            (contributionCapacityReopeningActionSourceVisitAt oldVisit
              sourceIndex).current)) :=
  contributionCapacityU8GeneratedResidual oldVisit

def contributionCapacityReopeningActionSourceAuthorityAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (contributionCapacityReopeningActionSourceRootAt oldVisit)
      (contributionCapacityReopeningActionSourceVisitAt oldVisit sourceIndex)
      (contributionCapacityReopeningActionSourceEntryAt oldVisit sourceIndex) :=
  contributionCapacityU8RuntimeAuthorityAt oldVisit sourceIndex

def contributionCapacityReopeningActionExactSourceEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ReopeningSourceEventAt oldVisit sourceIndex :=
  (contributionCapacityReopeningActionSourceRootAt oldVisit)
    |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (contributionCapacityReopeningActionSourceVisitAt oldVisit sourceIndex)

@[simp] theorem contributionCapacityReopeningActionSourceEntry_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    contributionCapacityReopeningActionSourceEntryAt oldVisit sourceIndex =
      contributionCapacityU8GeneratedResidual oldVisit :=
  rfl

@[simp] theorem contributionCapacityReopeningActionExactSource_occurrence
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityReopeningActionExactSourceEventAt oldVisit sourceIndex).occurrence =
      (CapacityU8RootAt oldVisit).emitted
        (contributionCapacityU8RuntimeVisitAt oldVisit sourceIndex).current :=
  rfl

def contributionCapacityReopeningActionOccurrencePresentationAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ConstructivePresentation
      ((CapacityU8RootAt oldVisit).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (contributionCapacityU8RuntimeVisitAt oldVisit sourceIndex).current)
      ((contributionCapacityReopeningAuthoritativeRoot oldVisit sourceIndex
        (contributionCapacityReopeningActionExactSourceEventAt oldVisit
          sourceIndex)).toRoot.actual.OccurrenceAt
            (contributionCapacityReopeningAuthoritativeRoot oldVisit sourceIndex
              (contributionCapacityReopeningActionExactSourceEventAt oldVisit
                sourceIndex)).toRoot.source.initial) where
  forward := fun _ => contributionCapacityReopeningEmitted oldVisit sourceIndex
    (contributionCapacityReopeningActionExactSourceEventAt oldVisit sourceIndex)
    0
  backward := fun _ => (CapacityU8RootAt oldVisit).emitted
    (contributionCapacityU8RuntimeVisitAt oldVisit sourceIndex).current
  backward_forward := by
    intro occurrence
    exact (contributionCapacityU8Occurrence_eq_emitted oldVisit occurrence).symm
  forward_backward := by
    intro occurrence
    exact (contributionCapacityReopeningOccurrence_eq_emitted oldVisit
      sourceIndex
      (contributionCapacityReopeningActionExactSourceEventAt oldVisit
        sourceIndex) occurrence).symm

@[simp] theorem contributionCapacityReopeningActionOccurrence_commutes
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityReopeningActionOccurrencePresentationAt oldVisit
      sourceIndex).forward
        (contributionCapacityReopeningActionExactSourceEventAt oldVisit
          sourceIndex).occurrence =
      (contributionCapacityReopeningAuthoritativeRoot oldVisit sourceIndex
        (contributionCapacityReopeningActionExactSourceEventAt oldVisit
          sourceIndex)).emitted
            (contributionCapacityReopeningAuthoritativeRoot oldVisit sourceIndex
              (contributionCapacityReopeningActionExactSourceEventAt oldVisit
                sourceIndex)).toRoot.source.initial :=
  rfl

end
end M14SourceGeneratedContributionCapacityReopeningActionSource
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningActionSource.contributionCapacityReopeningActionSourceAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningActionSource.contributionCapacityReopeningActionOccurrencePresentationAt
