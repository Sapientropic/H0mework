import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.Action

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (data : Continuation.FinancialData frame) (reader : Reader input depth count)
  (sourceBasis : Inquiry.Basis frame.N)
  (visit : SourceNativeTemporalVisitAt (sourceRoot frame data reader sourceBasis).toAuthoritativeRoot.toLedgerRoot)
  (germ : GermAt frame data reader visit.current)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (sourceRoot frame data reader sourceBasis)
    visit (sourceEntry frame data reader sourceBasis visit))

def program : SourceNativeSequentialActualActionProgramAt (sourceRoot frame data reader sourceBasis)
    visit (sourceEntry frame data reader sourceBasis visit) authority where
  targetAt := targetAt frame data reader sourceBasis visit germ authority

def sourceEvent := (sourceRoot frame data reader sourceBasis).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt visit

def generated := (program frame data reader sourceBasis visit germ authority).generate
  (sourceEvent frame data reader sourceBasis visit)

def nextVisit : SourceNativeTemporalVisitAt
    (targetRoot frame data reader sourceBasis visit germ).toAuthoritativeRoot.toLedgerRoot :=
  (SourceNativeTemporalVisitAt.finite (targetInitial frame data reader sourceBasis visit germ)).next
    (firstSuccessor frame data reader sourceBasis visit germ).next_eq

def nextEntry := (targetRoot frame data reader sourceBasis visit germ).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
  (firstSuccessor frame data reader sourceBasis visit germ).next_eq
  ((initialLedger frame data reader germ).forward (sourceEntry frame data reader sourceBasis visit))

def nextAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (targetRoot frame data reader sourceBasis visit germ)
    (nextVisit frame data reader sourceBasis visit germ)
    (nextEntry frame data reader sourceBasis visit germ) :=
  (generated frame data reader sourceBasis visit germ authority).target.targetAuthority

theorem whole_target_law_is_fixed_before_first_write :
    (generated frame data reader sourceBasis visit germ authority).target.targetRoot =
      (installCompleteFrame (bareFrame frame data reader germ) (financialData frame data reader germ)
        reader (basis frame data reader germ)).root := rfl

theorem action_returns_the_literal_next_visit :
    (generated frame data reader sourceBasis visit germ authority).target.targetAnswerAndNext.nextCurrent =
      ⟨(bareFrame frame data reader germ).V,
        (targetRoot frame data reader sourceBasis visit germ).toAuthoritativeRoot,
        nextVisit frame data reader sourceBasis visit germ⟩ :=
  (generated frame data reader sourceBasis visit germ authority).target.canonical_targetNextVisit_eq

theorem next_visit_is_the_source_body_target :
    (nextVisit frame data reader sourceBasis visit germ).current = bodyNext frame data reader germ :=
  first_target_is_the_same_body_next frame data reader sourceBasis visit germ

theorem next_visit_keeps_the_original_complete_account :
    (nextVisit frame data reader sourceBasis visit germ).current.account = frame.account visit.current := by
  rw [next_visit_is_the_source_body_target]
  exact first_body_retains_the_complete_original_account frame data reader germ

theorem answer_retains_the_original_typed_source_result :
    (generated frame data reader sourceBasis visit germ authority).answer = reportAt frame data reader germ := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.nextAuthority
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.action_returns_the_literal_next_visit
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Target.next_visit_keeps_the_original_complete_account
