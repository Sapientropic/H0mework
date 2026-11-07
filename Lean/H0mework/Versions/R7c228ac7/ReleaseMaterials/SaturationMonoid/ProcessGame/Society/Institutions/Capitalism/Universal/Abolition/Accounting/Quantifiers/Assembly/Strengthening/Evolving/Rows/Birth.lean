import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Rows.Paid
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootDebtAdmissionActualActionKernel

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger

noncomputable section

private theorem cast_preserves_claim_budget {N : WorldRelationNetwork} {left right : N.Support}
    (same : left = right) (row : OpenResponsibilityAt N left) :
    (same ▸ row : OpenResponsibilityAt N right).claim = row.claim ∧
      (same ▸ row : OpenResponsibilityAt N right).progressBudget = row.progressBudget := by cases same; exact ⟨rfl,rfl⟩

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  {root : SourceNativeLivingRootClosure N V}
  {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
  {entry : OpenResponsibilityAt N (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current)}
  {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}
  {program : SourceNativeDebtAdmissionActualActionProgramAt root visit entry authority}
  {event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit}
  (generated : SourceGeneratedDebtAdmissionActualActionAt program event)
  (rows : PaidRowsAt N (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current))

local notation "target" => generated.target

theorem birthInitialSupport_eq :
    (target).targetRoot.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt
      (target).targetRoot.toAuthoritativeRoot.toRoot.source.initial =
        (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current,some (target).sourceState) :=
  (target).initialSupport_eq.trans (congrArg (fun support => (support,some (target).sourceState))
    (by rw [event.eq_generated]; rfl))

def birthInitialRow (old : OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current)) :
    OpenResponsibilityAt (target).TargetN ((target).targetRoot.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt
      (target).targetRoot.toAuthoritativeRoot.toRoot.source.initial) :=
  (birthInitialSupport_eq generated).symm ▸
    oldEntry (N := N) (law := (target).law) (state? := some (target).sourceState) old

theorem birthInitialRow_claim_budget (old : OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt visit.current)) :
    (birthInitialRow generated old).claim = .inl old.claim ∧
      (birthInitialRow generated old).progressBudget = old.progressBudget :=
  cast_preserves_claim_budget (N := (target).TargetN) (birthInitialSupport_eq generated).symm _

def birthInitialRows : PaidRowsAt (target).TargetN
    ((target).targetRoot.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt
      (target).targetRoot.toAuthoritativeRoot.toRoot.source.initial) where
  productive := birthInitialRow generated rows.productive
  gross := birthInitialRow generated rows.gross
  productive_zero := (birthInitialRow_claim_budget generated rows.productive).2.trans rows.productive_zero
  gross_zero := (birthInitialRow_claim_budget generated rows.gross).2.trans rows.gross_zero
  different_claims := by
    rw [(birthInitialRow_claim_budget generated rows.productive).1,(birthInitialRow_claim_budget generated rows.gross).1]
    intro same
    exact rows.different_claims (Sum.inl.inj same)

def afterBirth : PaidRowsAt (target).TargetN
    ((target).targetRoot.toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt (target).targetVisit.current) :=
  nextPaidRows (target).targetRoot (target).targetInitialVisit (target).firstSuccessor (birthInitialRows generated rows)

theorem birth_preserves_both_original_claims :
    (afterBirth generated rows).productive.claim = .inl rows.productive.claim ∧
      (afterBirth generated rows).gross.claim = .inl rows.gross.claim :=
  ⟨(nextPaidRows_preserves_both_original_claims (target).targetRoot (target).targetInitialVisit
      (target).firstSuccessor (birthInitialRows generated rows)).1.trans (birthInitialRow_claim_budget generated rows.productive).1,
    (nextPaidRows_preserves_both_original_claims (target).targetRoot (target).targetInitialVisit
      (target).firstSuccessor (birthInitialRows generated rows)).2.trans (birthInitialRow_claim_budget generated rows.gross).1⟩

theorem neither_original_claim_is_the_fresh_native_claim :
    (afterBirth generated rows).productive.claim ≠ .inr (target).law.debtClaim ∧
      (afterBirth generated rows).gross.claim ≠ .inr (target).law.debtClaim := by
  rw [(birth_preserves_both_original_claims generated rows).1,(birth_preserves_both_original_claims generated rows).2]
  constructor <;> intro impossible <;> cases impossible

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
