import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.State
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Successor

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
  (frame : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

namespace Frame

def controlledPresentation := Abolition.Functions.Revision.InitialAdmission.Inquiry.presentation
  frame.package (.finite frame.visit) frame.authority

theorem ordinary_controlled_successor_valid
    (work : Inquiry.HasWork frame.package.source frame.visit.current)
    (absent : headRegistration? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current = none) :
    frame.ordinary.controlledPresentation.erase =
        (RootInquiryProcessNode.answered frame.controlledPresentation (.internal work)).erase ∧
      (RootInquiryProcessNode.active frame.controlledPresentation).PreservesGeneratedLivingLawAt
        (.internal work) (.active frame.ordinary.controlledPresentation) := by
  apply RootInquiryProcessNode.active_directlyAnswered_successor_valid
    frame.controlledPresentation frame.ordinary.controlledPresentation (.internal work)
    (Inquiry.answerFace frame.package (.finite frame.visit) work)
    (Inquiry.consumer frame.package (.finite frame.visit) work
      (Inquiry.no_registration_is_ordinary frame.package (.finite frame.visit) absent))
  · exact Inquiry.source_selected_ordinary frame.package (.finite frame.visit) frame.authority work absent
  · exact frame.ordinary_erase
  · exact HEq.rfl

theorem born_controlled_successor_valid
    (work : Inquiry.HasWork frame.package.source frame.visit.current)
    (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current)
    (selected : headRegistration? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current = some registered) :
    (frame.born registered).controlledPresentation.erase =
        (RootInquiryProcessNode.answered frame.controlledPresentation (.internal work)).erase ∧
      (RootInquiryProcessNode.active frame.controlledPresentation).PreservesGeneratedLivingLawAt
        (.internal work) (.active (frame.born registered).controlledPresentation) := by
  apply RootInquiryProcessNode.active_debtAdmission_successor_valid
    frame.controlledPresentation (frame.born registered).controlledPresentation (.internal work)
    (Inquiry.debtCore frame.package (.finite frame.visit) frame.authority registered)
  · exact Inquiry.source_selected_debt_core frame.package (.finite frame.visit) frame.authority work registered selected
  · exact frame.born_erase registered
  · exact HEq.rfl

end Frame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
