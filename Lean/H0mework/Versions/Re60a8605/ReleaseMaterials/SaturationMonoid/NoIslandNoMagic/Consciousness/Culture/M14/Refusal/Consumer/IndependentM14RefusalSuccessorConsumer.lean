import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface.SourceNativeM14RefusalSuccessorCoordinates
import H0mework.Foundation.Relations.ConsumerQuotient

/-!
# Independent refusal-successor consumer

The existing institutional culture consumers are restricted to the canonical
platform authority face at the right-Payment boundary.  The generated refusal
source/target outer occurrences therefore collide in the old view.  A new
independent readout records the actual successor current, response action,
employment-action trace code, and live/full-capture capacities.

The escape and all no-power-minting obligations are proved before any refusal
culture carrier, quotient, factorization, or root installation is imported.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Refusal
namespace Consumer

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedContributionCapacityEssentialAccessChannel
open ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation
open ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo
open ProcessGame.Society.M14ProofCarryingPaidSuccessorAfterRefusalAntiRetaliationRegression
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface

noncomputable section

/-- Both temporal sides retain the same already installed platform culture
face; their new difference belongs to the paid successor. -/
def m14RefusalOldInstitutionalViewAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14RefusalOccurrenceAt oldVisit sourceIndex boundary →
      M14InstitutionalChannelOccurrenceAt boundary :=
  fun _occurrence => m14InstitutionalPlatformOccurrenceAt boundary

def m14RefusalAuthorityReadoutAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IndependentReadout
      (M14RefusalOccurrenceAt oldVisit sourceIndex boundary) where
  Output := M14RefusalAuthorityReadout
  read := m14RefusalAuthorityReadAt oldVisit sourceIndex boundary

def m14RefusalReindexedInstitutionalConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary).reindex
    (m14RefusalOldInstitutionalViewAt oldVisit sourceIndex boundary)

def m14RefusalCultureConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14RefusalReindexedInstitutionalConsumersAt oldVisit sourceIndex boundary
    ).adjoin (m14RefusalAuthorityReadoutAt oldVisit sourceIndex boundary)

@[simp] theorem m14RefusalOldInstitutionalView_source_eq_target
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14RefusalOldInstitutionalViewAt oldVisit sourceIndex boundary
        (m14RefusalSourceOccurrenceAt oldVisit sourceIndex boundary) =
      m14RefusalOldInstitutionalViewAt oldVisit sourceIndex boundary
        (m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary) :=
  rfl

theorem m14RefusalAuthorityKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14RefusalOldInstitutionalViewAt oldVisit sourceIndex boundary)
      (m14RefusalAuthorityReadoutAt oldVisit sourceIndex boundary) :=
  ⟨m14RefusalSourceOccurrenceAt oldVisit sourceIndex boundary,
    m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary,
    m14RefusalOldInstitutionalView_source_eq_target oldVisit sourceIndex
      boundary,
    m14Refusal_source_target_difference oldVisit sourceIndex boundary⟩

theorem m14RefusalAuthority_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14RefusalAuthorityReadAt oldVisit sourceIndex boundary)
      (m14RefusalOldInstitutionalViewAt oldVisit sourceIndex boundary) :=
  (m14RefusalAuthorityKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

/-- Existing no-go family: no policy, service, administrative label,
employment action, or full-capture replay may mint capture/response authority
for the target. -/
theorem m14RefusalNoPowerMinting_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let index := m14RefusalSuccessorIndexAt boundary
    type_of% (paidSuccessorAfterRefusalAntiRetaliationAuditAt oldVisit
        sourceIndex index) ∧
      (∀ label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
          Bool,
        ¬ Nonempty
          (Observer.AuthorityFactorization
            (administrativeRetaliationObserver oldVisit sourceIndex label))) ∧
      IsEmpty (ExactAfterRefusalOwnPolicyPriceRecaptureAt oldVisit sourceIndex
        index) ∧
      (∀ channel : EssentialAccessChannel,
        IsEmpty (ExactAfterRefusalServiceRecaptureAt oldVisit sourceIndex
          index channel)) ∧
      IsEmpty (ExactAfterRefusalAdministrativeRecaptureAt oldVisit sourceIndex
        index) ∧
      IsEmpty (ExactAfterRefusalEmploymentRetaliationRecaptureAt oldVisit
        sourceIndex index) ∧
      IsEmpty (ExactAfterRefusalFullCaptureReportedNonretaliatoryAt oldVisit
        sourceIndex index) ∧
      IsEmpty
        (ExactPaidSuccessorFullCaptureRetaliationCountermodelAt oldVisit
            sourceIndex index →
          ExactAfterRefusalFullCaptureReportedNonretaliatoryAt oldVisit
            sourceIndex index) ∧
      type_of%
        (SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt.targetProtectedInterest_noChannelAuthority
          (oldVisit := oldVisit) (sourceIndex := sourceIndex) (index := index)) := by
  let index := m14RefusalSuccessorIndexAt boundary
  let anti := m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
  exact
    ⟨paidSuccessorAfterRefusalAntiRetaliationAuditAt oldVisit sourceIndex
        index,
      fun label => administrativeRetaliation_noAuthorityFactorization anti
        label,
      afterRefusalOwnPolicyPriceRecapture_isEmpty oldVisit sourceIndex index,
      afterRefusalServiceRecapture_isEmpty oldVisit sourceIndex index,
      afterRefusalAdministrativeRecapture_isEmpty oldVisit sourceIndex index,
      afterRefusalEmploymentRetaliationRecapture_isEmpty oldVisit sourceIndex
        index,
      afterRefusalFullCaptureReportedNonretaliatory_isEmpty oldVisit
        sourceIndex index,
      fullCaptureCountermodelCannotReconstructNonretaliatoryReplay oldVisit
        sourceIndex index,
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt.targetProtectedInterest_noChannelAuthority
        (oldVisit := oldVisit) (sourceIndex := sourceIndex) (index := index)⟩

theorem m14RefusalSuccessorConsumer_grounded
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (sourceGeneratedM14RefusalSuccessor_directConsumer oldVisit
        sourceIndex boundary) ∧
      type_of% (m14RefusalNoPowerMinting_directConsumer oldVisit sourceIndex
        boundary) ∧
      Function.Injective
        (m14RefusalAuthorityReadAt oldVisit sourceIndex boundary) ∧
      type_of% (m14RefusalAuthorityKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14RefusalAuthority_oldFactorization_isEmpty oldVisit
        sourceIndex boundary) :=
  ⟨sourceGeneratedM14RefusalSuccessor_directConsumer oldVisit sourceIndex
      boundary,
    m14RefusalNoPowerMinting_directConsumer oldVisit sourceIndex boundary,
    m14RefusalAuthorityRead_injective oldVisit sourceIndex boundary,
    m14RefusalAuthorityKernelEscapeAt oldVisit sourceIndex boundary,
    m14RefusalAuthority_oldFactorization_isEmpty oldVisit sourceIndex
      boundary⟩

end
end Consumer
end Refusal
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Consumer.m14RefusalAuthorityKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Consumer.m14RefusalAuthority_oldFactorization_isEmpty
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Consumer.m14RefusalNoPowerMinting_directConsumer
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Consumer.m14RefusalSuccessorConsumer_grounded
