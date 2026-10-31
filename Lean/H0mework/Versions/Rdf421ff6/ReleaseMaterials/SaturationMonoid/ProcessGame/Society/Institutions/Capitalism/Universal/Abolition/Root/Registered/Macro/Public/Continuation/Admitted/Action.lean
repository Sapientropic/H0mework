import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Target

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
  (complete : ¬ Inquiry.HasWork frame atCurrent.actual)
  (entry : OpenResponsibilityAt frame.N (frame.sourceSupport visit.current))
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit entry)

def program : SourceNativeSequentialActualActionProgramAt frame.root visit entry authority where
  targetAt := targetAt origin admission frame visit atCurrent reader complete entry authority

def sourceEvent := frame.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt visit

def generated := (program origin admission frame visit atCurrent reader complete entry authority).generate
  (sourceEvent frame visit)

def nextVisit : SourceNativeTemporalVisitAt
    (targetRoot origin admission frame visit atCurrent reader).toAuthoritativeRoot.toLedgerRoot :=
  (SourceNativeTemporalVisitAt.finite (targetInitial origin admission frame visit atCurrent reader)).next
    (firstSuccessor origin admission frame visit atCurrent reader).next_eq

def nextEntry := (targetRoot origin admission frame visit atCurrent reader).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
  (firstSuccessor origin admission frame visit atCurrent reader).next_eq
  ((initialLedger origin admission frame atCurrent reader).forward entry)

def nextAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (targetRoot origin admission frame visit atCurrent reader)
    (nextVisit origin admission frame visit atCurrent reader)
    (nextEntry origin admission frame visit atCurrent reader entry) :=
  (generated origin admission frame visit atCurrent reader complete entry authority).target.targetAuthority

theorem the_action_returns_the_actual_next_visit :
    (generated origin admission frame visit atCurrent reader complete entry authority).target.targetAnswerAndNext.nextCurrent =
      ⟨(targetFrame origin admission frame visit atCurrent reader).V,
        (targetRoot origin admission frame visit atCurrent reader).toAuthoritativeRoot,
        nextVisit origin admission frame visit atCurrent reader⟩ :=
  (generated origin admission frame visit atCurrent reader complete entry authority).target.canonical_targetNextVisit_eq

theorem the_returned_visit_keeps_the_original_complete_account :
    (nextVisit origin admission frame visit atCurrent reader).current.account = atCurrent.actual.account := by
  change (firstSuccessor origin admission frame visit atCurrent reader).targetCurrent.account = _
  rw [first_target_is_the_actual_selected_body]
  rfl

theorem the_action_retains_the_original_typed_public_report :
    (generated origin admission frame visit atCurrent reader complete entry authority).answer = atCurrent.rawAnswer reader := rfl

#print axioms program
#print axioms nextAuthority
#print axioms the_action_returns_the_actual_next_visit
#print axioms the_returned_visit_keeps_the_original_complete_account

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted
