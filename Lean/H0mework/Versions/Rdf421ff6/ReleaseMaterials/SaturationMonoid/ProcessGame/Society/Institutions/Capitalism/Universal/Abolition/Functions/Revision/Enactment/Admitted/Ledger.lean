import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Admitted.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Ingress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Admitted

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

private def sameSupportLedger {N : WorldRelationNetwork} {before after : N.Support}
    (same : after = before) : ConstructiveRetract (OpenResponsibilityAt N before) (OpenResponsibilityAt N after) := by
  cases same
  exact ⟨id, id, fun _ => rfl⟩

private theorem sameSupportLedger_heq {N : WorldRelationNetwork} {before after : N.Support}
    (same : after = before) : HEq (sameSupportLedger same)
      ((Financial.Installation.Ingress.identityTranslation N).oldOpenLedger before) := by
  cases same
  exact HEq.rfl

private theorem sameSupportLedger_rows {N : WorldRelationNetwork} {before after : N.Support}
    (same : after = before) :
    (∀ entry, ((sameSupportLedger same).forward entry).1 = entry.1) ∧
    (∀ entry, ((sameSupportLedger same).forward entry).claim = entry.claim) ∧
    (∀ entry, ((sameSupportLedger same).forward entry).progressBudget = entry.progressBudget) ∧
    (∀ entry, (sameSupportLedger same).forward ((sameSupportLedger same).backward entry) = entry) := by
  cases same
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (context : Context (input := input) (review := review) depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (admission : InitialAdmissionAt context)

abbrev translation := Financial.Installation.Ingress.identityTranslation context.native.N

def initialLedger : ConstructiveRetract
    (OpenResponsibilityAt context.native.N (context.native.sourceSupport context.visit.current))
    (OpenResponsibilityAt context.native.N
      ((root context admission).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        ((root context admission).emitted (initial context)))) :=
  sameSupportLedger (initial_support_is_the_literal_original_current context admission)

theorem initial_ledger_is_the_original_identity : HEq (initialLedger context admission)
    ((translation context).oldOpenLedger (context.native.sourceSupport context.visit.current)) :=
  sameSupportLedger_heq (initial_support_is_the_literal_original_current context admission)

theorem initial_ledger_preserves_every_original_row
    (entry : OpenResponsibilityAt context.native.N (context.native.sourceSupport context.visit.current)) :
    ((initialLedger context admission).forward entry).1 = entry.1 ∧
      ((initialLedger context admission).forward entry).claim = entry.claim ∧
      ((initialLedger context admission).forward entry).progressBudget = entry.progressBudget :=
  ⟨(sameSupportLedger_rows (initial_support_is_the_literal_original_current context admission)).1 entry,
    (sameSupportLedger_rows (initial_support_is_the_literal_original_current context admission)).2.1 entry,
    (sameSupportLedger_rows (initial_support_is_the_literal_original_current context admission)).2.2.1 entry⟩

theorem initial_ledger_has_no_fresh_row
    (entry : OpenResponsibilityAt context.native.N
      ((root context admission).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        ((root context admission).emitted (initial context)))) :
    (initialLedger context admission).forward ((initialLedger context admission).backward entry) = entry :=
  (sameSupportLedger_rows (initial_support_is_the_literal_original_current context admission)).2.2.2 entry

def initialRow (entry : OpenResponsibilityAt context.native.N (context.native.sourceSupport context.visit.current)) :
    ((root context admission).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (firstVisit context admission))).GeneratedEntryRowAt ((initialLedger context admission).forward entry) :=
  Macro.Public.Source.generatedRow input depth count prefixLimit renewalLimit (oldPast context) (InitialAdmission.start admission)
    (family context) (.finite (firstVisit context admission)) ((initialLedger context admission).forward entry)

#print axioms initial_ledger_preserves_every_original_row
#print axioms initialRow

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Admitted
