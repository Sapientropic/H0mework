import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Input.Source

/-! Lift the original registered failure through the input coface.  Its
physical occurrence, complete ledger, causal authority and successor are
unchanged; only the source-owned query vocabulary has been extended. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M9ProofCarryingRenewalInquiryRoot M14SourceGeneratedContributionMergeActionSource

variable {Party Good Port Technology Instrument : Type}
  (datum : Datum Party Good Port Technology Instrument)
  (oldVisit : OldVisit) (sourceIndex boundary : Nat)

def visit : SourceNativeTemporalVisitAt (root datum).toAuthoritativeRoot.toLedgerRoot :=
  FreshPayment.visit oldVisit sourceIndex boundary

def authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (root datum) (visit datum oldVisit sourceIndex boundary) M9ProofCarryingRenewalU8Failure.entry :=
  (FreshPayment.authority oldVisit sourceIndex boundary).withProjectionCoface (component datum)

def failureFace : SourceNativeRootExpressibilityFailureFaceAt
    (root datum).toAuthoritativeRoot (visit datum oldVisit sourceIndex boundary)
    (U7 := RootInquiryU8CompletionRegression.U7) RootInquiryU8CompletionRegression.failure where
  lawSurface_eq := (FreshPayment.failureFace oldVisit sourceIndex boundary).lawSurface_eq
  projection := (inherited datum).embed
    (FreshPayment.failureFace oldVisit sourceIndex boundary).projection
  active := (FreshPayment.failureFace oldVisit sourceIndex boundary).active
  classifier_eq := (FreshPayment.failureFace oldVisit sourceIndex boundary).classifier_eq
  calculus := (FreshPayment.failureFace oldVisit sourceIndex boundary).calculus
  u7Event := (FreshPayment.failureFace oldVisit sourceIndex boundary).u7Event
  u7Event_eq_emit := (FreshPayment.failureFace oldVisit sourceIndex boundary).u7Event_eq_emit
  theoryAudit := (FreshPayment.failureFace oldVisit sourceIndex boundary).theoryAudit
  support_eq := (FreshPayment.failureFace oldVisit sourceIndex boundary).support_eq
  rootEntry := (FreshPayment.failureFace oldVisit sourceIndex boundary).rootEntry
  rootEntryAtFailure_eq := (FreshPayment.failureFace oldVisit sourceIndex boundary).rootEntryAtFailure_eq
  rootDispositionCommutes := (FreshPayment.failureFace oldVisit sourceIndex boundary).rootDispositionCommutes
  project_heq := (FreshPayment.failureFace oldVisit sourceIndex boundary).project_heq

abbrev Query := GermAt datum ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current)

def frontier :=
  SourceNativeInquiryCofaceFrontierAt.ofRootFailureFace
    (root := root datum) (visit := visit datum oldVisit sourceIndex boundary)
    (U7 := RootInquiryU8CompletionRegression.U7)
    (calculus := RootInquiryU8CompletionRegression.theoryAuditCalculus)
    (oldTheory := RootInquiryU8CompletionRegression.oldTheory)
    (query := germAt datum ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))
    (event := ULift.up.{1, 0} ((root datum).emitted
      (visit datum oldVisit sourceIndex boundary).current))
    (entry := M9ProofCarryingRenewalU8Failure.entry)
    (authority := authority datum oldVisit sourceIndex boundary)
    (obstruction := RootInquiryU8CompletionRegression.obstruction)
    (u7Gate := RootInquiryU8CompletionRegression.u7Gate)
    (failure := RootInquiryU8CompletionRegression.failure)
    (failureFace datum oldVisit sourceIndex boundary) rfl
    (M9ProofCarryingRenewalU8Failure.successorAt
      (FreshPayment.bridge oldVisit sourceIndex boundary).rightRootVisit)

theorem original_row_and_successor_preserved :
    (frontier datum oldVisit sourceIndex boundary).rooted.oldTargetEntry =
      (FreshPayment.frontier oldVisit sourceIndex boundary).rooted.oldTargetEntry ∧
    HEq (frontier datum oldVisit sourceIndex boundary).rooted.oldSuccessor
      (FreshPayment.frontier oldVisit sourceIndex boundary).rooted.oldSuccessor := ⟨rfl, HEq.rfl⟩

theorem failure_source_is_same_original_row :
    (failureFace datum oldVisit sourceIndex boundary).rootEntry =
      (FreshPayment.failureFace oldVisit sourceIndex boundary).rootEntry := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource
