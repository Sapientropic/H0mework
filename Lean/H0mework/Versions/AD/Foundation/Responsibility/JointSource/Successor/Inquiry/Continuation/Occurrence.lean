import H0mework.Versions.AD.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Source

/-! Both source-selected successors consume their existing generated root
receipt before the canonical macro registry is assembled. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation
open SourceOperationEffects RootInquiryCompletion
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

namespace Frame
variable (frame : Frame (Value := Value) (Var := Var) (sort := sort))

private theorem selected_valid (selected : frame.Action)
    (query : (frame.presentationFrom selected).Query) :
    (frame.nextFrom selected).presentation.erase =
      (RootInquiryProcessNode.answered (frame.presentationFrom selected) query).erase ∧
    (RootInquiryProcessNode.active (frame.presentationFrom selected)).PreservesGeneratedLivingLawAt
      query (.active (frame.nextFrom selected).presentation) := by
  cases selected with
  | inr paid =>
      cases query
      apply RootInquiryProcessNode.active_directlyAnswered_successor_valid
        frame.currentPresentation frame.mathNext.presentation PUnit.unit
        (Inquiry.mathAnswerFace frame.old frame.registered frame.packetAt frame.depth)
        (Inquiry.mathConsumer frame.old frame.registered frame.packetAt frame.depth)
        (Inquiry.math_compiles frame.old frame.registered frame.packetAt frame.depth)
      · refine frame.mathNext.presentation_erase.trans ?_
        apply congrArg (fun current =>
          (⟨CompilerFromPacketSourceLaw.World frame.registered, current⟩ : AnyAuthoritativeRootCurrent.{u}))
        symm
        apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
        rfl
      · exact frame.mathNext.presentation_root
  | inl settled =>
      cases query
      apply RootInquiryProcessNode.active_debtAdmission_successor_valid
        frame.birthPresentation frame.born.presentation PUnit.unit
        ((Inquiry.residualBirthProgram frame.old frame.registered frame.packetAt frame.environment frame.depth).generate
          (frame.currentState.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt frame.currentState.visit))
        (Inquiry.birth_compiles frame.old frame.registered frame.packetAt frame.environment frame.depth)
      · refine frame.born.presentation_erase.trans ?_
        exact (congrArg (fun current =>
          (⟨CompilerFromPacketSourceLaw.World frame.request, current⟩ : AnyAuthoritativeRootCurrent.{u}))
          (Inquiry.Consumer.born_next frame.old frame.registered frame.packetAt frame.environment frame.depth)).symm
      · exact frame.born.presentation_root

theorem successor_valid (query : frame.presentation.Query) :
    frame.next.presentation.erase =
      (RootInquiryProcessNode.answered frame.presentation query).erase ∧
    (RootInquiryProcessNode.active frame.presentation).PreservesGeneratedLivingLawAt
      query (.active frame.next.presentation) := selected_valid frame frame.action query

end Frame
end RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
