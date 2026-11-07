import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Query

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {admission : Abolition.Functions.Revision.InitialAdmissionAt origin}
  (frame : Frame origin admission)

theorem ordinary_erase (work : frame.HasWork)
    (noIssue : Accounting.registration? input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual = none) :
    (frame.ordinary work noIssue).presentation.erase =
      (⟨frame.full.N, frame.full.root.generatedNextCurrentAt (.finite frame.visit)⟩ : AnyAuthoritativeRootCurrent) := by
  rw [Macro.Ingress.next_is_the_same_generated_successor frame.full.root (.finite frame.visit)
    (frame.full.successor frame.visit.current)]
  rfl

theorem born_erase
    (registered : Accounting.Registration input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual) :
    (frame.born registered).presentation.erase =
      (⟨(Inquiry.debtCore frame.source frame.reader (.finite frame.visit) frame.actual frame.authority registered).target.TargetN,
        (Inquiry.debtCore frame.source frame.reader (.finite frame.visit) frame.actual frame.authority registered).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) := by
  rw [(Inquiry.debtCore frame.source frame.reader (.finite frame.visit) frame.actual frame.authority registered).target.targetAnswerAndNext_next_eq]
  rfl

theorem reenter_erase (complete : ¬ frame.HasWork) :
    (frame.reenter complete).presentation.erase =
      (⟨(Inquiry.rawCore origin admission frame.source frame.reader (.finite frame.visit) frame.actual frame.authority complete).target.TargetN,
        (Inquiry.rawCore origin admission frame.source frame.reader (.finite frame.visit) frame.actual frame.authority complete).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) :=
  (congrArg (fun current => (⟨frame.full.N, current⟩ : AnyAuthoritativeRootCurrent))
    (Continuation.Admitted.the_action_returns_the_actual_next_visit origin admission frame.full (.finite frame.visit)
      frame.actualForFull frame.reader complete (frame.full.entry frame.visit.current) frame.authority)).symm

theorem successor_valid (query : frame.presentation.Query) :
    (frame.next.presentation.erase = (RootInquiryProcessNode.answered frame.presentation query).erase) ∧
      (RootInquiryProcessNode.active frame.presentation).PreservesGeneratedLivingLawAt
        query (RootInquiryProcessNode.active frame.next.presentation) := by
  have unique := frame.query_unique query
  cases unique
  by_cases work : frame.HasWork
  · rw [next, dif_pos work]
    unfold internalNext
    split
    · rename_i registered parsed
      apply RootInquiryProcessNode.active_debtAdmission_successor_valid
        frame.presentation (frame.born registered).presentation frame.query
        (Inquiry.debtCore frame.source frame.reader (.finite frame.visit) frame.actual frame.authority registered)
      · change Inquiry.compileUnit origin admission frame.source frame.reader (.finite frame.visit) frame.actual frame.authority = _
        have actualWork : Inquiry.HasWork frame.source frame.actual.actual := work
        simp only [Inquiry.compileUnit, dif_pos actualWork]
        split
        · rename_i selected found
          have same := Option.some.inj (found.symm.trans parsed)
          cases same
          rfl
        · rename_i absent
          cases absent.symm.trans parsed
      · exact frame.born_erase registered
      · exact HEq.rfl
    · rename_i parsed
      apply RootInquiryProcessNode.active_directlyAnswered_successor_valid
        frame.presentation (frame.ordinary work parsed).presentation frame.query
        (Inquiry.answerFace frame.source frame.reader (.finite frame.visit) frame.actual work)
        (Inquiry.consumer frame.source frame.reader (.finite frame.visit) frame.actual work parsed)
      · change Inquiry.compileUnit origin admission frame.source frame.reader (.finite frame.visit) frame.actual frame.authority = _
        have actualWork : Inquiry.HasWork frame.source frame.actual.actual := work
        simp only [Inquiry.compileUnit, dif_pos actualWork]
        split
        · rename_i selected found
          cases found.symm.trans parsed
        · rfl
      · exact frame.ordinary_erase work parsed
      · exact HEq.rfl
  · rw [next, dif_neg work]
    apply RootInquiryProcessNode.active_actualAction_successor_valid
      frame.presentation (frame.reenter work).presentation frame.query
      (Inquiry.rawCore origin admission frame.source frame.reader (.finite frame.visit) frame.actual frame.authority work)
    · change Inquiry.compileUnit origin admission frame.source frame.reader (.finite frame.visit) frame.actual frame.authority = _
      have complete : ¬ Inquiry.HasWork frame.source frame.actual.actual := work
      simp only [Inquiry.compileUnit, dif_neg complete]
      rfl
    · exact frame.reenter_erase work
    · exact HEq.rfl

#print axioms ordinary_erase
#print axioms born_erase
#print axioms reenter_erase
#print axioms successor_valid

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame
