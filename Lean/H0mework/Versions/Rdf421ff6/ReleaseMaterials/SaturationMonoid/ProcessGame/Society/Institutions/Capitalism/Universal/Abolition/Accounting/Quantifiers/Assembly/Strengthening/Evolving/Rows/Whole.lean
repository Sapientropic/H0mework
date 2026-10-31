import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Rows.Sequential
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Rows.Birth

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  {root : SourceNativeLivingRootClosure N V}
  {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
  {entry : OpenResponsibilityAt N (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current)}
  {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}
  {event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit}

section Sequential
variable {program : SourceNativeSequentialActualActionProgramAt root visit entry authority}
  (generated : SourceGeneratedSequentialActualActionAt program event)
  (old : OpenResponsibilityAt N (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current))
local notation "T" => generated.target

def sequentialRow : OpenResponsibilityAt (T).TargetN
    ((T).targetRoot.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt (T).targetVisit.current) :=
  nextRow (T).targetRoot (T).targetInitialVisit (T).firstSuccessor ((T).initialOpenLedger.forward old)

theorem sequentialRow_claim : (sequentialRow generated old).claim = (T).translation.claim.forward old.claim :=
  (nextRow_keeps_claim_and_never_refills (T).targetRoot (T).targetInitialVisit (T).firstSuccessor
    ((T).initialOpenLedger.forward old)).1.trans ((T).initialLedger_claim_commutes old).symm

theorem sequentialRow_budget : (sequentialRow generated old).progressBudget ≤ old.progressBudget :=
  (nextRow_keeps_claim_and_never_refills (T).targetRoot (T).targetInitialVisit (T).firstSuccessor
    ((T).initialOpenLedger.forward old)).2.trans ((T).initialLedger_budget_conservative old)
end Sequential

section Birth
variable {program : SourceNativeDebtAdmissionActualActionProgramAt root visit entry authority}
  (generated : SourceGeneratedDebtAdmissionActualActionAt program event)
  (old : OpenResponsibilityAt N (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current))
local notation "T" => generated.target

def bornRow : OpenResponsibilityAt (T).TargetN
    ((T).targetRoot.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt (T).targetVisit.current) :=
  nextRow (T).targetRoot (T).targetInitialVisit (T).firstSuccessor (birthInitialRow generated old)

theorem bornRow_claim : (bornRow generated old).claim = Sum.inl old.claim :=
  (nextRow_keeps_claim_and_never_refills (T).targetRoot (T).targetInitialVisit (T).firstSuccessor
    (birthInitialRow generated old)).1.trans (birthInitialRow_claim_budget generated old).1

theorem bornRow_budget : (bornRow generated old).progressBudget ≤ old.progressBudget :=
  (nextRow_keeps_claim_and_never_refills (T).targetRoot (T).targetInitialVisit (T).firstSuccessor
    (birthInitialRow generated old)).2.trans_eq (birthInitialRow_claim_budget generated old).2
end Birth
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
