import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Source

/-! The actual math or residual-birth occurrence generates its own complete
next-root receipt. This consumer precedes the macro registry's erasure proof. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
open SourceOperationEffects RootInquiryCompletion

noncomputable section
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
        (Inquiry.mathAnswerFace frame.old frame.program frame.registered frame.depth)
        (Inquiry.mathConsumer frame.old frame.program frame.registered frame.depth)
        (Inquiry.math_compiles frame.old frame.program frame.registered frame.depth)
      · refine frame.mathNext.presentation_erase.trans ?_
        apply congrArg (fun current => (⟨World frame.registered, current⟩ : AnyAuthoritativeRootCurrent.{u}))
        symm
        apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
        rfl
      · exact frame.mathNext.presentation_root
  | inl settled =>
      cases query
      apply RootInquiryProcessNode.active_debtAdmission_successor_valid
        frame.birthPresentation frame.born.presentation PUnit.unit frame.birthGenerated frame.birth_compiles
      · refine frame.born.presentation_erase.trans ?_
        exact (congrArg (fun current =>
          (⟨World frame.request, current⟩ : AnyAuthoritativeRootCurrent.{u}))
          (Inquiry.generated_math_next frame.currentState
            (Inquiry.nextProgram frame.old frame.program frame.registered) frame.request
            PUnit.unit (frame.currentState.authorityAt PUnit.unit)
            frame.firstStep frame.firstStep_generated _)).symm
      · exact frame.born.presentation_root

theorem successor_valid (query : frame.presentation.Query) :
    frame.next.presentation.erase =
      (RootInquiryProcessNode.answered frame.presentation query).erase ∧
    (RootInquiryProcessNode.active frame.presentation).PreservesGeneratedLivingLawAt
      query (.active frame.next.presentation) := selected_valid frame frame.action query

end Frame
end
end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
