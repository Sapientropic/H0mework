import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Morphism.Producer.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism

/-!
# Observer first-row authority has no free later installation

The observer-submission coordinate is installed by a pre-emitter law whose
active fibre is literally `current = 0`.  Every later revised temporal visit
has current `n + 1`, so the same coordinate cannot silently replay its
first-row authority incidence there.

This no-go does not deny the revised root's causal ledger authority.  It
rejects only a later `SourceInstalledRenewalAt` of this observer coordinate;
fresh social action must be generated at a new paid occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverFirstRowNoFreeEternity

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8

/-- At every strictly later revised visit, the first-row observer renewal
installation fibre is empty. -/
theorem observerSubmissionRenewal_afterFirst_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary laterIndex : Nat) :
    IsEmpty
      (SourceInstalledRenewalAt
        (renewalRecognitionAt oldVisit sourceIndex boundary)
        (revisedTemporalVisitAt oldVisit sourceIndex boundary
          (laterIndex + 1))) := by
  constructor
  intro installed
  have current_eq_zero :
      (show Nat from
        (revisedVisitAt oldVisit sourceIndex boundary
          (laterIndex + 1)).current) = 0 :=
    installed.active.down
  rw [revisedVisit_current_exact] at current_eq_zero
  omega

/-- The strongest aggregate no-free-eternity mouth: no positive finite
successor depth admits a replay of the first-row observer coordinate. -/
theorem observerSubmissionRenewal_onlyAtFirst
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∀ laterIndex : Nat,
      IsEmpty
        (SourceInstalledRenewalAt
          (renewalRecognitionAt oldVisit sourceIndex boundary)
          (revisedTemporalVisitAt oldVisit sourceIndex boundary
            (laterIndex + 1))) :=
  observerSubmissionRenewal_afterFirst_isEmpty oldVisit sourceIndex boundary

end
end M14SourceGeneratedPostSettlementObserverFirstRowNoFreeEternity
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFirstRowNoFreeEternity.observerSubmissionRenewal_afterFirst_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFirstRowNoFreeEternity.observerSubmissionRenewal_onlyAtFirst
