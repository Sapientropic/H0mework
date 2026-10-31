import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRoot

/-!
# Same-row U8 failure in the expanded joint root

The original inquiry/failure projection coordinates are inherited into the
pre-emitter renewal uplift.  This file re-generates causal row authority,
failure face, rooted failure, and minimal coface with literal `jointRoot`
indices throughout.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M9ProofCarryingRenewalU8Failure

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open ConstructiveRoot.RootInquiryU8CompletionRegression
open M9ProofCarryingRenewalInquiryRoot

abbrev N := M9ProofCarryingRenewalInquiryRoot.N
abbrev V := M9ProofCarryingRenewalInquiryRoot.V
abbrev U7 := RootInquiryU8CompletionRegression.U7

def entry : OpenResponsibilityAt N true :=
  RootInquiryU8CompletionRegression.entry

theorem entry_eq (candidate : OpenResponsibilityAt N true) :
    entry = candidate := by
  rcases candidate with ⟨responsibility, openReceipt⟩
  cases responsibility
  cases openReceipt
  rfl

def entryRowAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    (jointRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite visit)).GeneratedEntryRowAt entry :=
  ((jointRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (.finite visit)).canonicalGeneratedEntryRow? entry).get (by rfl)

private def initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    jointRoot
      (.finite jointRoot.toAuthoritativeRoot.toRoot.initialVisit) entry :=
  ((SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial?
    jointRoot entry .initial).get (by rfl)).2

private def authorityAtHistory :
    {current : V.Current} →
    (history : jointRoot.toAuthoritativeRoot.toRoot.ReachableAt current) →
    SourceNativeLivingTemporalCausalEntryAuthorityAt jointRoot
      (.finite ⟨current, history⟩) entry
  | _, .initial => initialAuthority
  | _, .step prior next_eq => by
      let priorAuthority := authorityAtHistory prior
      let nextAuthority := priorAuthority.next next_eq
      exact entry_eq _ ▸ nextAuthority

def authorityAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      jointRoot (.finite visit) entry :=
  authorityAtHistory visit.history

theorem theoryAuditRootDispositionCommutesAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    U7DemandEntryRootDispositionCommutesAt
      RootInquiryU8CompletionRegression.theoryAuditCalculus
      (RootInquiryU8CompletionRegression.theoryAuditCalculus.source.emit
        RootInquiryU8CompletionRegression.obstruction)
      entry
      ((jointRoot.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile
        (jointRoot.emitted visit.current)).entryDisposition entry) :=
  RootInquiryU8CompletionRegression.theoryAuditRootDispositionCommutes

/-- Exact inherited failure coordinate of the expanded source inventory. -/
def failureFaceAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeRootExpressibilityFailureFaceAt
    jointRoot.toAuthoritativeRoot (.finite visit) (U7 := U7)
      RootInquiryU8CompletionRegression.failure where
  lawSurface_eq := rfl
  projection := M9ProofCarryingRenewalInquiryRoot.jointFailureProjection
  active := ()
  classifier_eq := rfl
  calculus := RootInquiryU8CompletionRegression.theoryAuditCalculus
  u7Event := RootInquiryU8CompletionRegression.theoryAuditCalculus.source.emit
    RootInquiryU8CompletionRegression.obstruction
  u7Event_eq_emit := rfl
  theoryAudit := RootInquiryU8CompletionRegression.u7Gate
  support_eq := rfl
  rootEntry := entry
  rootEntryAtFailure_eq := rfl
  rootDispositionCommutes := theoryAuditRootDispositionCommutesAt visit
  project_heq := HEq.rfl

def successorAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    CausalEntrySuccessorAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot (.finite visit) entry :=
  CausalEntrySuccessorAt.ofNonterminal rfl

def rootedAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    RootedActualExpressibilityFailureAt
    jointRoot.toAuthoritativeRoot (.finite visit) U7
      RootInquiryU8CompletionRegression.failure :=
  RootedActualExpressibilityFailureAt.ofRootFailureFace
    (failureFaceAt visit) (authorityAt visit).toAuthoritativeAuthority
      (successorAt visit)

def cofaceAt (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    GeneratedMinimalCofaceAt (rootedAt visit) :=
  root_obstruction_generates_minimal_coface (rootedAt visit)

/-! ## Initial-visit facade -/

def entryRow :
    (jointRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      jointVisit).GeneratedEntryRowAt entry :=
  entryRowAt jointRoot.toAuthoritativeRoot.toRoot.initialVisit

def authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    jointRoot jointVisit entry :=
  authorityAt jointRoot.toAuthoritativeRoot.toRoot.initialVisit

theorem theoryAuditRootDispositionCommutes :
    U7DemandEntryRootDispositionCommutesAt
      RootInquiryU8CompletionRegression.theoryAuditCalculus
      (RootInquiryU8CompletionRegression.theoryAuditCalculus.source.emit
        RootInquiryU8CompletionRegression.obstruction)
      entry
      ((jointRoot.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile
        (jointRoot.emitted jointVisit.current)).entryDisposition entry) :=
  theoryAuditRootDispositionCommutesAt
    jointRoot.toAuthoritativeRoot.toRoot.initialVisit

/-- Initial specialization retained for all existing downstream consumers. -/
def failureFace : SourceNativeRootExpressibilityFailureFaceAt
    jointRoot.toAuthoritativeRoot jointVisit (U7 := U7)
      RootInquiryU8CompletionRegression.failure :=
  failureFaceAt jointRoot.toAuthoritativeRoot.toRoot.initialVisit

def successor : CausalEntrySuccessorAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot jointVisit entry :=
  successorAt jointRoot.toAuthoritativeRoot.toRoot.initialVisit

def rooted : RootedActualExpressibilityFailureAt
    jointRoot.toAuthoritativeRoot jointVisit U7
      RootInquiryU8CompletionRegression.failure :=
  rootedAt jointRoot.toAuthoritativeRoot.toRoot.initialVisit

def coface : GeneratedMinimalCofaceAt rooted :=
  cofaceAt jointRoot.toAuthoritativeRoot.toRoot.initialVisit

abbrev NewN := coface.worldNetwork

@[simp] theorem rooted_entry_eq_installedRenewal :
    rooted.rootEntry = installedRenewal.payload.sourceEntry :=
  rfl

@[simp] theorem rooted_oldWorld_is_literal_jointRoot :
    rooted.oldBoundaryEvolution =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
        jointVisit :=
  rfl

end
end M9ProofCarryingRenewalU8Failure
end Society
end ProcessGame
end SaturationMonoid
