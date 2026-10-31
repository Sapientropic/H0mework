import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct.Body
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Ledger

set_option autoImplicit false

open private sameSupportLedger sameSupportLedger_heq sameSupportLedger_rows from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Ledger

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
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
  {visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot}
  (atCurrent : Public.Inquiry.ActualAt frame visit.current)
  (reader : Macro.Raw.Reader input depth count)

abbrev translation := Financial.Installation.Ingress.identityTranslation frame.N

def initialLedger : ConstructiveRetract
    (OpenResponsibilityAt frame.N (frame.sourceSupport visit.current))
    (OpenResponsibilityAt frame.N ((bareFrame frame atCurrent reader).sourceSupport (bodyInitial frame atCurrent))) :=
  sameSupportLedger (initial_support_is_the_actual_current frame atCurrent reader)

theorem initial_ledger_is_the_original_identity : HEq (initialLedger frame atCurrent reader)
    ((translation frame).oldOpenLedger (frame.sourceSupport visit.current)) :=
  sameSupportLedger_heq (initial_support_is_the_actual_current frame atCurrent reader)

theorem initial_ledger_preserves_every_original_row
    (entry : OpenResponsibilityAt frame.N (frame.sourceSupport visit.current)) :
    ((initialLedger frame atCurrent reader).forward entry).1 = entry.1 ∧
      ((initialLedger frame atCurrent reader).forward entry).claim = entry.claim ∧
      ((initialLedger frame atCurrent reader).forward entry).progressBudget = entry.progressBudget :=
  ⟨(sameSupportLedger_rows (initial_support_is_the_actual_current frame atCurrent reader)).1 entry,
    (sameSupportLedger_rows (initial_support_is_the_actual_current frame atCurrent reader)).2.1 entry,
    (sameSupportLedger_rows (initial_support_is_the_actual_current frame atCurrent reader)).2.2.1 entry⟩

theorem initial_ledger_has_no_fresh_row
    (entry : OpenResponsibilityAt frame.N ((bareFrame frame atCurrent reader).sourceSupport (bodyInitial frame atCurrent))) :
    (initialLedger frame atCurrent reader).forward ((initialLedger frame atCurrent reader).backward entry) = entry :=
  (sameSupportLedger_rows (initial_support_is_the_actual_current frame atCurrent reader)).2.2.2 entry

def initialRow (entry : OpenResponsibilityAt frame.N (frame.sourceSupport visit.current)) :
    ((bareFrame frame atCurrent reader).root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (bareFrame frame atCurrent reader).root.toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt
        ((initialLedger frame atCurrent reader).forward entry) :=
  Public.Source.generatedRow input depth count prefixLimit renewalLimit oldPast (selectedStart frame atCurrent reader)
    (family frame atCurrent) (.finite (bareFrame frame atCurrent reader).root.toAuthoritativeRoot.toRoot.initialVisit)
    ((initialLedger frame atCurrent reader).forward entry)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct
