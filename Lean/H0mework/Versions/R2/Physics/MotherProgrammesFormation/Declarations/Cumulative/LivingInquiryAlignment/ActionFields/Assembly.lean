import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.Body
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Fibers

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionBody
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}
    {TargetN : WorldRelationNetwork.{0}} {TargetV : ConstructiveRoot.Vocabulary.{0}}
    {targetRoot : SourceNativeLivingRootClosure TargetN TargetV}

local notation "Target" => SourceNativeSequentialActualActionTargetAt root visit event entry authority

/-- An inverse schema supplies only the original field types. Its actual
answer and receipt must be read from the formed dependent point. -/
def assemble (body : Body (root := root) (visit := visit) (event := event) (entry := entry) targetRoot)
    (I : Type) (F : I → Type 3) (selected : Sigma F) : Target where
  TargetN := TargetN
  translation := body.values.translation
  TargetV := TargetV
  targetRoot := targetRoot
  targetTheory := targetRoot.source.base.lawSurface
  lawSurface_heq := HEq.rfl
  targetTheory_rootSemantic := MotherActionRecovery.semanticTranslation _
  occurrencePresentation := body.values.occurrencePresentation
  occurrence_commutes := body.checked.occurrence
  initialSupport_heq := heq_of_eq body.values.initialSupport_eq
  initialOpenLedger := body.values.initialOpenLedger
  initialOpenLedger_heq := body.values.initialOpenLedger_heq
  initialLedger_responsibility_commutes := body.checked.responsibility
  initialLedger_claim_commutes := body.checked.claim
  initialLedger_budget_conservative := body.checked.budget
  initialLedgerNoFresh := body.checked.noFresh
  translatedSourceEntryRow := body.values.row
  firstSuccessor := body.values.successor
  canonical_targetNextVisit_eq := body.checked.next_eq
  Answer := I
  answer := selected.1
  Receipt := F
  receipt := selected.2

def ofTarget (target : Target) :
    Body (root := root) (visit := visit) (event := event) (entry := entry) target.targetRoot where
  values := {
    translation := target.translation
    occurrencePresentation := target.occurrencePresentation
    initialSupport_eq := eq_of_heq target.initialSupport_heq
    initialOpenLedger := target.initialOpenLedger
    initialOpenLedger_heq := target.initialOpenLedger_heq
    row := target.translatedSourceEntryRow
    successor := target.firstSuccessor }
  checked := {
    occurrence := target.occurrence_commutes
    responsibility := target.initialLedger_responsibility_commutes
    claim := target.initialLedger_claim_commutes
    budget := target.initialLedger_budget_conservative
    noFresh := target.initialLedgerNoFresh
    next_eq := target.canonical_targetNextVisit_eq }

theorem assemble_ofTarget (target : Target) :
    assemble (ofTarget target) target.Answer target.Receipt ⟨target.answer, target.receipt⟩ = target := by
  cases target with
  | mk targetN translation targetV targetRoot theory lawSurface semantic occurrence occurrenceCommutes
      support ledger ledgerHeq responsibility claim budget noFresh row successor nextEq I answer F receipt =>
    have same := eq_of_heq lawSurface
    subst theory
    have recovered := MotherActionRecovery.semanticTranslation_recovers targetRoot.source.base.lawSurface semantic
    cases recovered
    rfl

/-- Complete actual-action target recovery uses all generated body fields
and the actual generated high-universe receipt point. -/
theorem target_recovers (target : Target)
    (body : Body (root := root) (visit := visit) (event := event) (entry := entry) target.targetRoot)
    (body_eq : body = ofTarget target)
    {rank : Ordinal.{3}} {value : MotherReceiptPayload.Value rank}
    (receipt : MotherReceiptPayload.Presentation target.Answer target.Receipt
      ⟨target.answer, target.receipt⟩ value) :
    assemble body target.Answer target.Receipt receipt.restrict = target := by
  rw [body_eq, receipt.restrict_eq]
  exact assemble_ofTarget target

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionBody
