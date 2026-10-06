import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Target

/-! The source mathematical action chooses the actual compiler constructor.
Paid actions read the complete calculation result; settlement consumes the
source-generated residual admission with its exact heterogeneous target. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation
open RootInquiryCompletion SourceOperationEffects
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
namespace Shared
variable (configuration : Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

def compilation (candidate : Query frame configuration) : SourceNativeInquiryCompilationProgramAt (root frame configuration) (visit frame configuration)
    (base frame).U7 (base frame).calculus (root frame configuration).source.base.lawSurface candidate
    (ULift.up.{u + 1, u} (actualOccurrence frame)) (frame.currentState.entryAt PUnit.unit) (authority frame configuration) where
  compile := fun event => match frame.action with
    | .inr _ => .answered (resultFace frame configuration) (by
        cases query_unique frame configuration candidate
        exact consumer frame configuration)
    | .inl _ => .debtAdmission ((birthProgram frame configuration).generate event)

def state : RootInquiryStateAt
    (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered)
    (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt) where
  root := root frame configuration
  visit := visit frame configuration
  U7 := (base frame).U7
  calculus := (base frame).calculus
  Query := Query frame configuration
  entryAt := fun _ => frame.currentState.entryAt PUnit.unit
  authorityAt := fun _ => authority frame configuration
  compilationProgramAt := compilation frame configuration
  compilationFaceAt := fun candidate => by
    have same := query_unique frame configuration candidate
    subst candidate
    refine { projection := (compilationInstallation frame configuration).embed PUnit.unit
             active := PUnit.unit
             classifier_eq := rfl
             project_heq := ?_ }
    change HEq _ (SourceNativeInquiryCompilationTokenAt.canonical
      ((compilation frame configuration (query frame configuration)).generate.output.answerReadout))
    unfold compilation
    cases frame.action <;> exact HEq.rfl
  u7RootDisposition_commutes := by
    intro candidate _ _ impossible
    have same := query_unique frame configuration candidate
    subst candidate
    change (match frame.action with
      | .inr _ => SourceNativeInquiryCompilationAt.answered (resultFace frame configuration) (consumer frame configuration)
      | .inl _ => SourceNativeInquiryCompilationAt.debtAdmission
          ((birthProgram frame configuration).generate ((root frame configuration).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (visit frame configuration)))).audit = _ at impossible
    generalize frame.action = selected at impossible
    cases selected <;> exact nomatch impossible

def presentation : RootInquiryStatePresentation where
  N := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered
  V := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt
  state := .create (state frame configuration)

def next : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort) :=
  match frame.action with
  | .inr _ => frame.mathNext
  | .inl _ => nextBorn frame configuration

theorem compiles_paid (paid : DebtActivationWorld.GeneratedStepAt
    (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment frame.registered.input.expression)
    frame.event.state) (actual : frame.action = .inr paid) :
    (state frame configuration).compileInquiry (query frame configuration) = .answered (resultFace frame configuration) (consumer frame configuration) := by
  change (match frame.action with
    | .inr _ => SourceNativeInquiryCompilationAt.answered (resultFace frame configuration) (consumer frame configuration)
    | .inl _ => SourceNativeInquiryCompilationAt.debtAdmission ((birthProgram frame configuration).generate _)) = _
  rw [actual]
  rfl

theorem compiles_settled (settled : SourceOperationExecutionDebt.Settlement frame.event.state)
    (actual : frame.action = .inl settled) :
    (state frame configuration).compileInquiry (query frame configuration) = .debtAdmission ((birthProgram frame configuration).generate
      ((root frame configuration).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (visit frame configuration))) := by
  change (match frame.action with
    | .inr _ => SourceNativeInquiryCompilationAt.answered (resultFace frame configuration) (consumer frame configuration)
    | .inl _ => SourceNativeInquiryCompilationAt.debtAdmission ((birthProgram frame configuration).generate _)) = _
  rw [actual]
  rfl

theorem successor_valid (candidate : (presentation frame configuration).Query) :
    (presentation (next frame configuration) configuration).erase = (RootInquiryProcessNode.answered (presentation frame configuration) candidate).erase ∧
    (RootInquiryProcessNode.active (presentation frame configuration)).PreservesGeneratedLivingLawAt
      candidate (.active (presentation (next frame configuration) configuration)) := by
  cases query_unique frame configuration candidate
  cases actual : frame.action with
  | inr paid =>
      apply RootInquiryProcessNode.active_directlyAnswered_successor_valid
        (presentation frame configuration) (presentation (next frame configuration) configuration) (query frame configuration) (resultFace frame configuration) (consumer frame configuration)
        (compiles_paid frame configuration paid actual)
      · unfold next
        rw [actual]
        apply congrArg (fun current => (⟨_, current⟩ : AnyAuthoritativeRootCurrent.{u}))
        symm
        apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
        rfl
      · unfold next
        rw [actual]
        exact HEq.rfl
  | inl settled =>
      apply RootInquiryProcessNode.active_debtAdmission_successor_valid
        (presentation frame configuration) (presentation (next frame configuration) configuration) (query frame configuration)
        ((birthProgram frame configuration).generate ((root frame configuration).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (visit frame configuration)))
        (compiles_settled frame configuration settled actual)
      · unfold next
        rw [actual]
        apply congrArg (fun current => (⟨_, current⟩ : AnyAuthoritativeRootCurrent.{u}))
        change _ = (targetAt frame configuration ((root frame configuration).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (visit frame configuration))).targetAnswerAndNext.nextCurrent
        exact (target_next frame configuration ((root frame configuration).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (visit frame configuration))).symm
      · unfold next
        rw [actual]
        exact HEq.rfl

end Shared

abbrev compilation := Shared.compilation frame originalProgramme
abbrev state := Shared.state frame originalProgramme
abbrev presentation := Shared.presentation frame originalProgramme
abbrev next := Shared.next frame originalProgramme
abbrev compiles_paid := Shared.compiles_paid frame originalProgramme
abbrev compiles_settled := Shared.compiles_settled frame originalProgramme
abbrev successor_valid := Shared.successor_valid frame originalProgramme

end SourceOperationInquiry.Context.Faces.Execution.Activation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
