import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct.Compilation.State

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

def nextActual : Public.Inquiry.ActualAt (recordedFrame frame atCurrent reader)
    (nextVisit frame visit atCurrent reader).current :=
  ⟨bodyNext frame atCurrent,congrArg some (first_target_is_the_actual_selected_body frame atCurrent reader)⟩

variable (complete : ¬ Public.Inquiry.HasWork frame atCurrent.actual)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current))

def nextInquiry := presentation (recordedFrame frame atCurrent reader) reader
  (nextVisit frame visit atCurrent reader) (nextActual frame visit atCurrent reader)
  (nextAuthorityForInstalledEntry frame visit atCurrent reader complete authority)

theorem the_generated_body_returns_a_live_native_query :
    (nextInquiry frame visit atCurrent reader complete authority).erase =
      ⟨frame.N,(generated frame visit atCurrent reader complete (frame.entry visit.current) authority).target.targetAnswerAndNext.nextCurrent⟩ := by
  exact congrArg (fun current => (⟨frame.N,current⟩ : AnyAuthoritativeRootCurrent))
    (the_current_source_returns_its_actual_next frame visit atCurrent reader complete (frame.entry visit.current) authority).symm

theorem the_actual_body_cannot_reset_the_original_financial_account :
    (nextActual frame visit atCurrent reader).actual.account = atCurrent.actual.account := rfl

theorem the_body_has_actually_been_paid : (nextActual frame visit atCurrent reader).actual.bodyPaid = true := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct
