import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Action.Installation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Account
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Compilation.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.CanonicalEntry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Action

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Abolition.Root.Registered.Macro.Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (actual : Public.Inquiry.ActualAt frame visit.current)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current))
  (reader : Macro.Raw.Reader input depth count)

local notation "C" => preparedContext frame visit actual authority
local notation "full" => fullFrame frame visit C reader
local notation "action" => generated frame visit actual authority reader

def nextVisit := (action).target.targetVisit

def nextActual : Public.Inquiry.ActualAt (bareFrame frame visit C) (nextVisit frame visit actual authority reader).current :=
  ⟨actual.actual,reentry_is_at_the_same_live_cursor frame visit actual C reader⟩

theorem initial_entry_is_the_same_native_row :
    (action).target.translatedSourceEntry = (full).entry (initialVisit frame visit C reader).current := by
  exact eq_of_heq (Factory.Public.next_keeps_the_complete_original_entry (sourceContext frame visit actual authority))

def initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (full).root
    (initialVisit frame visit C reader) ((full).entry (initialVisit frame visit C reader).current) :=
  initial_entry_is_the_same_native_row frame visit actual authority reader ▸ (action).target.initialAuthority

def nextAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (full).root
    (nextVisit frame visit actual authority reader) ((full).entry (nextVisit frame visit actual authority reader).current) :=
  Public.Accounting.Born.Action.nextAuthorityForInstalledEntry (full) (initialVisit frame visit C reader)
    (initialAuthority frame visit actual authority reader)

theorem the_source_item_is_not_consumed_by_reanchoring :
    (nextActual frame visit actual authority reader).actual = actual.actual := rfl

theorem the_complete_original_account_is_still_current :
    (nextActual frame visit actual authority reader).actual.account = actual.actual.account := rfl

theorem the_pending_registration_is_not_skipped :
    Public.Accounting.registration? input depth count prefixLimit renewalLimit oldPast start
        (nextActual frame visit actual authority reader).actual =
      Public.Accounting.registration? input depth count prefixLimit renewalLimit oldPast start actual.actual := rfl

variable {sourceDepth sourceCount : Nat} {review : Option (ReviewPhase.ContextAt input)}
  (origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)

def nativeInquiry := Public.Inquiry.presentation origin admission (bareFrame frame visit C) reader
  (nextVisit frame visit actual authority reader) (nextActual frame visit actual authority reader)
  (nextAuthority frame visit actual authority reader)

theorem actual_process_resumes_with_the_original_native_query :
    (RootInquiryProcessNode.answered (presentation frame visit actual authority reader) PUnit.unit).erase =
      (nativeInquiry frame visit actual authority reader origin admission).erase := by
  change (⟨frame.N,(action).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) = _
  exact congrArg (fun current => (⟨frame.N,current⟩ : AnyAuthoritativeRootCurrent)) (action).target.targetAnswerAndNext_next_eq

theorem the_resumed_compiler_is_the_original_native_selection :
    (Public.Inquiry.state origin admission (bareFrame frame visit C) reader
      (nextVisit frame visit actual authority reader) (nextActual frame visit actual authority reader)
      (nextAuthority frame visit actual authority reader)).compileInquiry PUnit.unit =
    Public.Inquiry.compileUnit origin admission (bareFrame frame visit C) reader
      (nextVisit frame visit actual authority reader) (nextActual frame visit actual authority reader)
      (nextAuthority frame visit actual authority reader) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Action
