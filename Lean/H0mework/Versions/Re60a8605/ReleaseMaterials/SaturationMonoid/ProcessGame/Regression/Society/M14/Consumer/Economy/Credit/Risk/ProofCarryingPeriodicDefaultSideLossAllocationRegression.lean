import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Credit.Risk.PeriodicDefaultSideLossAllocation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Credit.ProofCarryingPeriodicClearingCreditRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Credit.Risk.ProofCarryingDefaultSideLossAllocationRootRegression

/-!
# Direct consumer for periodic default-side loss allocation

At each finite old-root depth this Prop-only certificate consumes the existing
C6 credit certificate, the same-depth periodic default-side carrier, the
visit-indexed root-action certificate, and both exact child consumers.  Its
periodicity is inherited from the clearing-backstop occurrence; it introduces
no loss-allocation occurrence of its own.

This certificate does not assert canonical-runtime selection or resumption.
Only the separate depth-zero compatibility theorem identifies its
visit-indexed root certificate with the parent projection of the already
installed fixed certificate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPeriodicDefaultSideLossAllocationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8RevisedWorld
open M14UBIPeriodicRootHistory
open M14PeriodicClearingBackstopRenewal
open M14PeriodicClearingCreditClaimLifecycle
open M14ProofCarryingPeriodicClearingCreditRegression
open M14PeriodicDefaultSideLossAllocation
open M14ProofCarryingDefaultSideLossAllocationConsumers
open M14ProofCarryingDefaultSideLossAllocationRootRegression

/-! ## Depth-only direct certificate -/

structure ProofCarryingPeriodicDefaultSideLossAllocationCertificateAt
    (depth : Nat) : Prop where
  priorCredit : ProofCarryingPeriodicClearingCreditCertificateAt depth
  periodicCarrier : Nonempty
    (SourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt depth)
  carrierUsesExactDepthVisit :
    let carrier :=
      sourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt depth
    carrier.credit =
        sourceGeneratedProofCarryingPeriodicClearingCreditAt depth ∧
      carrier.visit = rootVisitAt depth ∧
      carrier.action =
        generatedDefaultSideLossAllocationAt (rootVisitAt depth)
  rootActionAtExactVisit :
    ProofCarryingDefaultSideLossAllocationRootCertificateAtVisit
      (rootVisitAt depth)
  leftChildConsumerAtExactVisit : Nonempty
    (SourceGeneratedDefaultSideChildConsumerAtVisit
      (rootVisitAt depth)
      (generatedDefaultSideLossAllocationAt (rootVisitAt depth)).left rfl)
  rightChildConsumerAtExactVisit : Nonempty
    (SourceGeneratedDefaultSideChildConsumerAtVisit
      (rootVisitAt depth)
      (generatedDefaultSideLossAllocationAt (rootVisitAt depth)).right
      (generatedDefaultSideLossAllocationAt
        (rootVisitAt depth)).origin_eq.symm)
  backstopOccurrenceInjective :
    Function.Injective periodicClearingBackstopOccurrenceAt
  adjacentBackstopOccurrencesDistinct :
    periodicClearingBackstopOccurrenceAt depth ≠
      periodicClearingBackstopOccurrenceAt (depth + 1)
  noSingleBackstopOccurrenceCarriesAllDepths :
    ¬ ∃ occurrence : AnyPeriodicClearingBackstopOccurrence,
      ∀ candidateDepth : Nat,
        periodicClearingBackstopOccurrenceAt candidateDepth = occurrence

/-- Sole public producer.  The caller selects only the already generated
finite depth; credit, visit, revised action, root certificate, child consumers,
and occurrence separation are all read from existing source producers. -/
theorem proofCarryingPeriodicDefaultSideLossAllocationDirectConsumer
    (depth : Nat) :
    ProofCarryingPeriodicDefaultSideLossAllocationCertificateAt depth where
  priorCredit := proofCarryingPeriodicClearingCreditDirectConsumer depth
  periodicCarrier :=
    every_depth_generates_defaultSideLossAllocation depth
  carrierUsesExactDepthVisit := ⟨rfl, rfl, rfl⟩
  rootActionAtExactVisit :=
    proofCarryingDefaultSideLossAllocationRootCertificateAtVisit
      (rootVisitAt depth)
  leftChildConsumerAtExactVisit :=
    ⟨leftChildConsumerAt (rootVisitAt depth)⟩
  rightChildConsumerAtExactVisit :=
    ⟨rightChildConsumerAt (rootVisitAt depth)⟩
  backstopOccurrenceInjective :=
    periodic_defaultSide_backstopOccurrence_injective
  adjacentBackstopOccurrencesDistinct :=
    adjacent_defaultSide_backstopOccurrences_distinct depth
  noSingleBackstopOccurrenceCarriesAllDepths :=
    no_single_backstop_occurrence_carries_all_defaultSide_depths

/-! ## Initial fixed-certificate compatibility -/

/-- At depth zero, and only at that fixed specialization, the periodic
certificate's visit-indexed root-action proof is the parent projection of the
already installed fixed certificate.  This theorem exports none of the fixed
runtime-resumption fields at positive depth. -/
theorem initial_rootActionCertificate_compatible_with_fixed :
    (proofCarryingPeriodicDefaultSideLossAllocationDirectConsumer 0
      ).rootActionAtExactVisit =
      (proofCarryingDefaultSideLossAllocationRootCertificate
        ).toProofCarryingDefaultSideLossAllocationRootCertificateAtVisit :=
  Subsingleton.elim _ _

/-- Interface control: the periodic direct certificate is a same-visit action
consumer, not a runtime-selection or runtime-resumption certificate. -/
theorem periodicDefaultSideCertificate_has_no_runtimeResumption_mouth
    (depth : Nat) : True := by
  let certificate :=
    proofCarryingPeriodicDefaultSideLossAllocationDirectConsumer depth
  fail_if_success exact certificate.runtimeFirstTickResolutionIsJointCore
  fail_if_success exact certificate.runtimeCofaceResumption
  fail_if_success exact certificate.runtimeFirstTickNextState
  fail_if_success exact certificate.runtimeFirstTickNextNode
  fail_if_success exact certificate.runtimeFirstTickPreservesActionRoot
  trivial

end
end M14ProofCarryingPeriodicDefaultSideLossAllocationRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicDefaultSideLossAllocationRegression.proofCarryingPeriodicDefaultSideLossAllocationDirectConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicDefaultSideLossAllocationRegression.initial_rootActionCertificate_compatible_with_fixed
