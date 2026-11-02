import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Inquiry.FailureReadback
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Internal
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.InitialReadback

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

variable (germ : Raw.GermAt frame.package.source frame.package.sourceData frame.package.reader frame.visit.current)

abbrev controlOrigin := Abolition.Functions.Revision.Enactment.Inquiry.contextAt
  frame.package (SourceNativeTemporalVisitAt.finite frame.visit) frame.authority germ

theorem raw_controlled_successor_valid
    (failed : Abolition.Functions.Revision.InitialObstructionAt (frame.controlOrigin germ))
    (selected : Abolition.Functions.Revision.InitialAdmission.select (frame.controlOrigin germ) = .obstructed failed) :
    (frame.reenter germ).controlledPresentation.erase =
        (RootInquiryProcessNode.answered frame.controlledPresentation (.raw germ)).erase ∧
      (RootInquiryProcessNode.active frame.controlledPresentation).PreservesGeneratedLivingLawAt
        (.raw germ) (.active (frame.reenter germ).controlledPresentation) := by
  apply RootInquiryProcessNode.active_actualAction_successor_valid
    frame.controlledPresentation (frame.reenter germ).controlledPresentation (.raw germ)
    (Abolition.Functions.Revision.InitialAdmission.Failure.generated (frame.controlOrigin germ) failed)
  · change Abolition.Functions.Revision.InitialAdmission.Inquiry.compilation
      frame.package (.finite frame.visit) frame.authority (.raw germ) = _
    simp only [Abolition.Functions.Revision.InitialAdmission.Inquiry.compilation, selected]
    rfl
  · exact (frame.reenter_erase germ).trans
      (congrArg (fun current => (⟨frame.package.source.N, current⟩ : AnyAuthoritativeRootCurrent))
        (Abolition.Functions.Revision.InitialAdmission.Failure.action_returns_the_original_actual_next
          (frame.controlOrigin germ) failed).symm)
  · exact HEq.rfl

theorem enactment_controlled_successor_valid
    (admission : Abolition.Functions.Revision.InitialAdmissionAt (frame.controlOrigin germ))
    (selected : Abolition.Functions.Revision.InitialAdmission.select (frame.controlOrigin germ) = .admitted admission) :
    (Public.Runtime.Frame.initial frame.package (.finite frame.visit) frame.authority germ admission).presentation.erase =
        (RootInquiryProcessNode.answered frame.controlledPresentation (.raw germ)).erase ∧
      (RootInquiryProcessNode.active frame.controlledPresentation).PreservesGeneratedLivingLawAt
        (.raw germ) (.active (Public.Runtime.Frame.initial frame.package (.finite frame.visit) frame.authority germ admission).presentation) := by
  apply RootInquiryProcessNode.active_actualAction_successor_valid
    frame.controlledPresentation (Public.Runtime.Frame.initial frame.package (.finite frame.visit) frame.authority germ admission).presentation
    (.raw germ) (Abolition.Functions.Revision.Enactment.Admitted.generated (frame.controlOrigin germ) admission)
  · exact Abolition.Functions.Revision.InitialAdmission.Inquiry.the_source_selected_enactment_is_the_actual_compiler_image
      frame.package (.finite frame.visit) frame.authority germ admission selected
  · exact Public.Runtime.Frame.initial_erase frame.package (.finite frame.visit) frame.authority germ admission
  · exact HEq.rfl

end Frame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
