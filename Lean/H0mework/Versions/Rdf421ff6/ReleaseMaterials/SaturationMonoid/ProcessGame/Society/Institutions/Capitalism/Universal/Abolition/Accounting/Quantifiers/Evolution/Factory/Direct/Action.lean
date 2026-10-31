import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct.Target

set_option autoImplicit false

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
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (atCurrent : Public.Inquiry.ActualAt frame visit.current)
  (reader : Macro.Raw.Reader input depth count)
  (complete : ¬ Public.Inquiry.HasWork frame atCurrent.actual)
  (entry : OpenResponsibilityAt frame.N (frame.sourceSupport visit.current))
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit entry)

def program : SourceNativeSequentialActualActionProgramAt frame.root visit entry authority where
  targetAt := targetAt frame visit atCurrent reader complete entry authority

def generated := (program frame visit atCurrent reader complete entry authority).generate
  (frame.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt visit)

def nextVisit : SourceNativeTemporalVisitAt (targetRoot frame atCurrent reader).toAuthoritativeRoot.toLedgerRoot :=
  (SourceNativeTemporalVisitAt.finite (targetInitial frame atCurrent reader)).next (firstSuccessor frame atCurrent reader).next_eq

def nextEntry := (targetRoot frame atCurrent reader).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
  (firstSuccessor frame atCurrent reader).next_eq ((initialLedger frame atCurrent reader).forward entry)

def nextAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (targetRoot frame atCurrent reader)
    (nextVisit frame visit atCurrent reader) (nextEntry frame visit atCurrent reader entry) :=
  (generated frame visit atCurrent reader complete entry authority).target.targetAuthority

theorem the_current_source_returns_its_actual_next :
    (generated frame visit atCurrent reader complete entry authority).target.targetAnswerAndNext.nextCurrent =
      ⟨(targetFrame frame atCurrent reader).V,(targetRoot frame atCurrent reader).toAuthoritativeRoot,nextVisit frame visit atCurrent reader⟩ :=
  (generated frame visit atCurrent reader complete entry authority).target.canonical_targetNextVisit_eq

theorem the_current_source_returns_its_literal_raw_result :
    (generated frame visit atCurrent reader complete entry authority).answer = atCurrent.rawAnswer reader := rfl

theorem the_new_body_preserves_the_whole_original_financial_account :
    (nextVisit frame visit atCurrent reader).current.account = atCurrent.actual.account := by
  change (firstSuccessor frame atCurrent reader).targetCurrent.account = _
  rw [first_target_is_the_actual_selected_body]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct
