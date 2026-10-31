import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Body
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.GeneratedRow
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Ingress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

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
  (origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  {current : frame.V.Current} (atCurrent : Inquiry.ActualAt frame current)
  (reader : Macro.Raw.Reader input depth count)

abbrev translation := Financial.Installation.Ingress.identityTranslation frame.N

def initialLedger : ConstructiveRetract
    (OpenResponsibilityAt frame.N (frame.sourceSupport current))
    (OpenResponsibilityAt frame.N
      ((bareFrame origin admission frame atCurrent reader).sourceSupport (bodyInitial frame atCurrent))) :=
  sameSupportLedger (initial_support_is_the_same_original_current origin admission frame atCurrent reader)

theorem initial_ledger_is_the_original_identity : HEq (initialLedger origin admission frame atCurrent reader)
    ((translation frame).oldOpenLedger (frame.sourceSupport current)) :=
  sameSupportLedger_heq (initial_support_is_the_same_original_current origin admission frame atCurrent reader)

theorem initial_ledger_preserves_every_original_row
    (entry : OpenResponsibilityAt frame.N (frame.sourceSupport current)) :
    ((initialLedger origin admission frame atCurrent reader).forward entry).1 = entry.1 ∧
      ((initialLedger origin admission frame atCurrent reader).forward entry).claim = entry.claim ∧
      ((initialLedger origin admission frame atCurrent reader).forward entry).progressBudget = entry.progressBudget :=
  ⟨(sameSupportLedger_rows (initial_support_is_the_same_original_current origin admission frame atCurrent reader)).1 entry,
    (sameSupportLedger_rows (initial_support_is_the_same_original_current origin admission frame atCurrent reader)).2.1 entry,
    (sameSupportLedger_rows (initial_support_is_the_same_original_current origin admission frame atCurrent reader)).2.2.1 entry⟩

theorem initial_ledger_has_no_fresh_row
    (entry : OpenResponsibilityAt frame.N
      ((bareFrame origin admission frame atCurrent reader).sourceSupport (bodyInitial frame atCurrent))) :
    (initialLedger origin admission frame atCurrent reader).forward
      ((initialLedger origin admission frame atCurrent reader).backward entry) = entry :=
  (sameSupportLedger_rows (initial_support_is_the_same_original_current origin admission frame atCurrent reader)).2.2.2 entry

def initialRow (entry : OpenResponsibilityAt frame.N (frame.sourceSupport current)) :
    ((bareFrame origin admission frame atCurrent reader).root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (bareFrame origin admission frame atCurrent reader).root.toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt
        ((initialLedger origin admission frame atCurrent reader).forward entry) :=
  Source.generatedRow input depth count prefixLimit renewalLimit oldPast
    (selectedStart frame atCurrent reader) (family frame atCurrent)
    (.finite (bareFrame origin admission frame atCurrent reader).root.toAuthoritativeRoot.toRoot.initialVisit)
    ((initialLedger origin admission frame atCurrent reader).forward entry)

#print axioms initial_ledger_preserves_every_original_row
#print axioms initialRow

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted
