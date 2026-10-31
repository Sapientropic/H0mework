import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Action
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.CanonicalEntry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

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
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (atCurrent : Inquiry.ActualAt frame visit.current)
  (reader : Macro.Raw.Reader input depth count)

theorem the_initial_row_is_the_same_installed_entry :
    (initialLedger origin admission frame atCurrent reader).forward (frame.entry visit.current) =
      (targetFrame origin admission frame visit atCurrent reader).entry
        (targetInitial origin admission frame visit atCurrent reader).current := by
  apply Financial.Installation.entry_eq_of_key _ _
  · exact (initial_ledger_preserves_every_original_row origin admission frame atCurrent reader
      (frame.entry visit.current)).1.trans (frame.family.entry_key _ _)
  · exact frame.family.open_fibres _

theorem the_next_row_is_the_same_installed_entry :
    nextEntry origin admission frame visit atCurrent reader (frame.entry visit.current) =
      (targetFrame origin admission frame visit atCurrent reader).entry
        (nextVisit origin admission frame visit atCurrent reader).current := by
  unfold nextEntry
  rw [the_initial_row_is_the_same_installed_entry origin admission frame visit atCurrent reader]
  exact Accounting.Born.Action.canonical_entry_is_the_same_installed_row
    (targetFrame origin admission frame visit atCurrent reader)
    (.finite (targetInitial origin admission frame visit atCurrent reader))

/-- The original row's causal authority reaches the row already installed
before this first write. Equality follows its original source keys. -/
def nextAuthorityForInstalledEntry (complete : ¬ Inquiry.HasWork frame atCurrent.actual)
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current)) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt (targetRoot origin admission frame visit atCurrent reader)
      (nextVisit origin admission frame visit atCurrent reader)
      ((targetFrame origin admission frame visit atCurrent reader).entry
        (nextVisit origin admission frame visit atCurrent reader).current) :=
  the_next_row_is_the_same_installed_entry origin admission frame visit atCurrent reader ▸
    nextAuthority origin admission frame visit atCurrent reader complete (frame.entry visit.current) authority

#print axioms the_next_row_is_the_same_installed_entry
#print axioms nextAuthorityForInstalledEntry

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted
