import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Continuation.Frame

/-! The original source compiler pays both successor branches. Its settled
relation selects the residual birth body at the same current, and the actual
birth receipt fixes the next complete living root. -/

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request.Continuation

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
        (mathAnswerFace frame.old frame.program frame.registered frame.scope frame.depth)
        (mathConsumer frame.old frame.program frame.registered frame.scope frame.depth)
        (math_compiles frame.old frame.program frame.registered frame.scope frame.depth)
      · refine frame.mathNext.presentation_erase.trans ?_
        apply congrArg (fun current => (⟨NewN frame.old frame.registered, current⟩ : AnyAuthoritativeRootCurrent.{u}))
        symm
        apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
        rfl
      · exact frame.mathNext.presentation_root
  | inl settled =>
      cases query
      let nextProgram := Request.nextProgram frame.old frame.program frame.registered frame.scope
      let nextScope := Request.nextScope frame.old frame.program frame.registered frame.scope
      let inputs := Residual.inputs frame.old frame.program frame.registered frame.scope frame.depth frame.environmentAt
      let owners := Residual.owners frame.old frame.program frame.registered frame.scope frame.depth frame.environmentAt
      let payments := Residual.payments frame.old frame.program frame.registered frame.scope frame.depth frame.environmentAt
      let actions := Residual.actions frame.old frame.program frame.registered frame.scope frame.depth frame.environmentAt
      let audits := Residual.audits frame.old frame.program frame.registered frame.scope frame.depth
      let generated := Request.generated frame.currentState nextProgram inputs nextScope owners payments actions PUnit.unit
      apply RootInquiryProcessNode.active_debtAdmission_successor_valid
        frame.birthPresentation frame.born.presentation PUnit.unit generated
        (birth_compiles frame.currentState nextProgram inputs nextScope owners payments actions audits PUnit.unit)
      · exact frame.born.presentation_erase.trans
          (birthProgramAt_next frame.currentState nextProgram inputs nextScope owners PUnit.unit
            (payments PUnit.unit) (actions PUnit.unit) _).symm
      · exact frame.born.presentation_root.trans
          (birthProgramAt_root frame.currentState nextProgram inputs nextScope owners PUnit.unit
            (payments PUnit.unit) (actions PUnit.unit) _).symm

theorem successor_valid (query : frame.presentation.Query) :
    frame.next.presentation.erase =
      (RootInquiryProcessNode.answered frame.presentation query).erase ∧
    (RootInquiryProcessNode.active frame.presentation).PreservesGeneratedLivingLawAt
      query (.active frame.next.presentation) := selected_valid frame frame.action query

end Frame
end
end RootGeneratedDebtActivationJointSource.Native.Request.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
