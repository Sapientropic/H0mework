import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct.Action
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.CanonicalEntry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (atCurrent : Public.Inquiry.ActualAt frame visit.current)
  (reader : Macro.Raw.Reader input depth count)

theorem the_initial_row_is_the_same_installed_entry :
    (initialLedger frame atCurrent reader).forward (frame.entry visit.current) =
      (targetFrame frame atCurrent reader).entry
        (targetInitial frame atCurrent reader).current := by
  apply Financial.Installation.entry_eq_of_key _ _
  · exact (initial_ledger_preserves_every_original_row frame atCurrent reader
      (frame.entry visit.current)).1.trans (frame.family.entry_key _ _)
  · exact frame.family.open_fibres _

theorem the_next_row_is_the_same_installed_entry :
    nextEntry frame visit atCurrent reader (frame.entry visit.current) =
      (targetFrame frame atCurrent reader).entry
        (nextVisit frame visit atCurrent reader).current := by
  unfold nextEntry
  rw [the_initial_row_is_the_same_installed_entry frame visit atCurrent reader]
  exact Public.Accounting.Born.Action.canonical_entry_is_the_same_installed_row
    (targetFrame frame atCurrent reader)
    (.finite (targetInitial frame atCurrent reader))

/-- The original row's causal authority reaches the row already installed
before this first write. Equality follows its original source keys. -/
def nextAuthorityForInstalledEntry (complete : ¬ Public.Inquiry.HasWork frame atCurrent.actual)
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current)) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt (targetRoot frame atCurrent reader)
      (nextVisit frame visit atCurrent reader)
      ((targetFrame frame atCurrent reader).entry
        (nextVisit frame visit atCurrent reader).current) :=
  the_next_row_is_the_same_installed_entry frame visit atCurrent reader ▸
    nextAuthority frame visit atCurrent reader complete (frame.entry visit.current) authority

#print axioms the_next_row_is_the_same_installed_entry
#print axioms nextAuthorityForInstalledEntry

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct
