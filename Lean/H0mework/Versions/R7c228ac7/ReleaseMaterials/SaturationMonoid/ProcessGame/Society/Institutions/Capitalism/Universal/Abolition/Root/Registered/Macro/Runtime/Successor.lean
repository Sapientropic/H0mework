import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

namespace Frame
variable (frame : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

theorem ordinary_erase : frame.ordinary.presentation.erase =
    (⟨frame.package.frame.N, frame.package.frame.root.generatedNextCurrentAt (.finite frame.visit)⟩ : AnyAuthoritativeRootCurrent) := by
  rw [Ingress.next_is_the_same_generated_successor frame.package.frame.root (.finite frame.visit)
    (frame.package.frame.successor frame.visit.current)]
  rfl

theorem born_erase
    (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current) :
    (frame.born registered).presentation.erase =
      (⟨(Inquiry.debtCore frame.package (.finite frame.visit) frame.authority registered).target.TargetN,
        (Inquiry.debtCore frame.package (.finite frame.visit) frame.authority registered).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) := by
  rw [(Inquiry.debtCore frame.package (.finite frame.visit) frame.authority registered).target.targetAnswerAndNext_next_eq]
  rfl

theorem reenter_erase
    (germ : Raw.GermAt frame.package.source frame.package.sourceData frame.package.reader frame.visit.current) :
    (frame.reenter germ).presentation.erase =
      (⟨(Inquiry.rawCore frame.package (.finite frame.visit) frame.authority germ).target.TargetN,
        (Inquiry.rawCore frame.package (.finite frame.visit) frame.authority germ).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) :=
  (congrArg (fun current => (⟨frame.package.source.N, current⟩ : AnyAuthoritativeRootCurrent))
    (Raw.Target.action_returns_the_literal_next_visit frame.package.source frame.package.sourceData frame.package.reader
      frame.package.basis (.finite frame.visit) germ frame.authority)).symm

theorem nextAt_successor_valid (query : frame.presentation.Query) :
    ((frame.nextAt query).presentation.erase = (RootInquiryProcessNode.answered frame.presentation query).erase) ∧
      (RootInquiryProcessNode.active frame.presentation).PreservesGeneratedLivingLawAt
        query (RootInquiryProcessNode.active (frame.nextAt query).presentation) := by
  cases query with
  | internal work =>
    dsimp only [nextAt]
    unfold internalNext
    cases selected : headRegistration? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current with
    | none =>
      apply RootInquiryProcessNode.active_directlyAnswered_successor_valid
        frame.presentation frame.ordinary.presentation (.internal work)
        (Inquiry.answerFace frame.package (.finite frame.visit) work)
        (Inquiry.consumer frame.package (.finite frame.visit) work
          (Inquiry.no_registration_is_ordinary frame.package (.finite frame.visit) selected))
      · exact Inquiry.source_selected_ordinary frame.package (.finite frame.visit) frame.authority work selected
      · exact frame.ordinary_erase
      · exact HEq.rfl
    | some registered =>
      apply RootInquiryProcessNode.active_debtAdmission_successor_valid
        frame.presentation (frame.born registered).presentation (.internal work)
        (Inquiry.debtCore frame.package (.finite frame.visit) frame.authority registered)
      · exact Inquiry.source_selected_debt_core frame.package (.finite frame.visit) frame.authority work registered selected
      · exact frame.born_erase registered
      · exact HEq.rfl
  | raw germ =>
      apply RootInquiryProcessNode.active_actualAction_successor_valid
        frame.presentation (frame.reenter germ).presentation (.raw germ)
        (Inquiry.rawCore frame.package (.finite frame.visit) frame.authority germ)
      · exact Inquiry.source_selected_raw frame.package (.finite frame.visit) frame.authority germ
      · exact frame.reenter_erase germ
      · exact HEq.rfl

theorem successor_valid (query : frame.presentation.Query) :
    (frame.next.presentation.erase = (RootInquiryProcessNode.answered frame.presentation query).erase) ∧
      (RootInquiryProcessNode.active frame.presentation).PreservesGeneratedLivingLawAt
        query (RootInquiryProcessNode.active frame.next.presentation) := by
  have sameNext : frame.nextAt query = frame.next := congrArg frame.nextAt (frame.query_unique query)
  simpa only [sameNext] using frame.nextAt_successor_valid query

#print axioms reenter_erase
#print axioms nextAt_successor_valid
#print axioms successor_valid

end Frame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
