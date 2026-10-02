import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Target

/-! The existing inquiry query and complete installed compilation face stay
literal. Actual paid requests change the compiler body at answered audits. -/

set_option autoImplicit false
universe u v

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry

open SourceOperationEffects DebtActivationWorld RootInquiryCompletion

noncomputable section

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (inputs : old.Query → RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (owners : (query : old.Query) → (inputs query).input.owner = old.entryAt query)

private def transportProgram {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {first second : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (same : first = second) (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit second)
    (source : SourceNativeDebtAdmissionActualActionProgramAt root visit first (same.symm ▸ authority)) :
    SourceNativeDebtAdmissionActualActionProgramAt root visit second authority := by
  cases same
  exact source

def birthProgramAt (query : old.Query)
    (paid : GeneratedStepAt (Idle.law (inputs query).input.environment (inputs query).input.expression)
      (initialEvent (inputs query)).state)
    (action : sourceAction old program (inputs query) = .inr paid) :
    SourceNativeDebtAdmissionActualActionProgramAt old.root old.visit (old.entryAt query) (old.authorityAt query) :=
  transportProgram (owners query) (old.authorityAt query)
    (birthProgram old query program (inputs query) ((owners query).symm ▸ old.authorityAt query) paid action)

private def compilationFromAction (query : old.Query)
    (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit)
    (selected : SourceOperationExecutionDebt.Settlement (initialEvent (inputs query)).state ⊕
      GeneratedStepAt (Idle.law (inputs query).input.environment (inputs query).input.expression)
        (initialEvent (inputs query)).state)
    (action : sourceAction old program (inputs query) = selected) :
    SourceNativeInquiryCompilationAt old.root old.visit old.U7 old.calculus
      old.root.toAuthoritativeRoot.source.lawSurface query (old.emitInquiry query)
      (old.entryAt query) (old.authorityAt query) := by
  cases selected with
  | inl _ => exact old.compileInquiry query
  | inr paid =>
      exact .debtAdmission ((birthProgramAt old program inputs owners query paid action).generate event)

def compilationAt (query : old.Query)
    (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    SourceNativeInquiryCompilationAt old.root old.visit old.U7 old.calculus
      old.root.toAuthoritativeRoot.source.lawSurface query (old.emitInquiry query)
      (old.entryAt query) (old.authorityAt query) :=
  match (old.compileInquiry query).audit with
  | .answered => compilationFromAction old program inputs owners query event
      (sourceAction old program (inputs query)) rfl
  | .obstructed _ _ => old.compileInquiry query

private theorem selected_eq {S : Type u} {C : Type v} (source : S)
    (body : (selected : S) → source = selected → C) (selected : S) (same : source = selected) :
    body source rfl = body selected same := by
  cases same
  rfl

theorem compilationAt_paid (query : old.Query)
    (paid : GeneratedStepAt (Idle.law (inputs query).input.environment (inputs query).input.expression)
      (initialEvent (inputs query)).state)
    (answered : (old.compileInquiry query).audit = .answered)
    (action : sourceAction old program (inputs query) = .inr paid)
    (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    compilationAt old program inputs owners query event =
      .debtAdmission ((birthProgramAt old program inputs owners query paid action).generate event) := by
  unfold compilationAt
  rw [answered]
  dsimp only
  exact selected_eq (sourceAction old program (inputs query))
    (compilationFromAction old program inputs owners query event) (.inr paid) action

private theorem compilationFromAction_audit (query : old.Query)
    (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit)
    (selected : SourceOperationExecutionDebt.Settlement (initialEvent (inputs query)).state ⊕
      GeneratedStepAt (Idle.law (inputs query).input.environment (inputs query).input.expression)
        (initialEvent (inputs query)).state)
    (action : sourceAction old program (inputs query) = selected)
    (answered : (old.compileInquiry query).audit = .answered) :
    (compilationFromAction old program inputs owners query event selected action).audit =
      (old.compileInquiry query).audit := by
  cases selected with
  | inl _ => rfl
  | inr paid => exact answered.symm

theorem compilation_audit (query : old.Query)
    (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    (compilationAt old program inputs owners query event).audit = (old.compileInquiry query).audit := by
  unfold compilationAt
  split
  · rename_i audit
    exact compilationFromAction_audit old program inputs owners query event _ rfl audit
  · rfl

private theorem program_answer {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {first second : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (same : first = second) (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit second)
    (source : SourceNativeDebtAdmissionActualActionProgramAt root visit first (same.symm ▸ authority))
    (event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit) :
    HEq (((transportProgram same authority source).generate event).target.answer)
      ((source.generate event).target.answer) := by
  cases same
  rfl

private theorem compilationFromAction_answer (query : old.Query)
    (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit)
    (selected : SourceOperationExecutionDebt.Settlement (initialEvent (inputs query)).state ⊕
      GeneratedStepAt (Idle.law (inputs query).input.environment (inputs query).input.expression)
        (initialEvent (inputs query)).state)
    (action : sourceAction old program (inputs query) = selected) :
    HEq (compilationFromAction old program inputs owners query event selected action).answerReadout
      (old.compileInquiry query).answerReadout := by
  cases selected with
  | inl _ => rfl
  | inr paid =>
      exact program_answer (owners query) (old.authorityAt query)
        (birthProgram old query program (inputs query) ((owners query).symm ▸ old.authorityAt query)
          paid action) event

theorem compilation_answer (query : old.Query)
    (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    HEq (compilationAt old program inputs owners query event).answerReadout
      (old.compileInquiry query).answerReadout := by
  unfold compilationAt
  split
  · exact compilationFromAction_answer old program inputs owners query event _ rfl
  · rfl

def compilationProgramAt (query : old.Query) : SourceNativeInquiryCompilationProgramAt
    old.root old.visit old.U7 old.calculus old.root.toAuthoritativeRoot.source.lawSurface
    query (old.emitInquiry query) (old.entryAt query) (old.authorityAt query) where
  compile := compilationAt old program inputs owners query

private theorem program_target {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {first second : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (same : first = second) (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit second)
    (source : SourceNativeDebtAdmissionActualActionProgramAt root visit first (same.symm ▸ authority))
    (event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit) :
    HEq (((transportProgram same authority source).generate event).target)
      ((source.generate event).target) := by
  cases same
  rfl

theorem birthProgramAt_target (query : old.Query)
    (paid : GeneratedStepAt (Idle.law (inputs query).input.environment (inputs query).input.expression)
      (initialEvent (inputs query)).state)
    (action : sourceAction old program (inputs query) = .inr paid)
    (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit) :
    HEq ((birthProgramAt old program inputs owners query paid action).generate event).target
      (targetAt old query program (inputs query) ((owners query).symm ▸ old.authorityAt query) paid action event) :=
  program_target (owners query) (old.authorityAt query)
    (birthProgram old query program (inputs query) ((owners query).symm ▸ old.authorityAt query) paid action) event

private theorem token_heq {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {theory : TheoryState N} {support : N.Support} {entry : OpenResponsibilityAt N support}
    {Query : Type u} {query : Query} {Event : Type (u + 1)} {event : Event}
    {leftAudit rightAudit : SourceNativeInquiryFrontAuditAt U7 calculus theory support}
    {Left Right : Type u} {left : Left} {right : Right}
    (audits : leftAudit = rightAudit) (answers : HEq left right) :
    HEq (SourceNativeInquiryCompilationTokenAt.canonical
      (entry := entry) (query := query) (event := event) (audit := leftAudit) left)
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := entry) (query := query) (event := event) (audit := rightAudit) right) := by
  cases audits
  cases answers
  rfl

def birthState : RootInquiryStateAt N V where
  root := old.root
  visit := old.visit
  U7 := old.U7
  calculus := old.calculus
  Query := old.Query
  entryAt := old.entryAt
  authorityAt := old.authorityAt
  compilationProgramAt := compilationProgramAt old program inputs owners
  compilationFaceAt := fun query =>
    { projection := (old.compilationFaceAt query).projection
      active := (old.compilationFaceAt query).active
      classifier_eq := (old.compilationFaceAt query).classifier_eq
      project_heq := (old.compilationFaceAt query).project_heq.trans
        (token_heq (compilation_audit old program inputs owners query _)
          (compilation_answer old program inputs owners query _)).symm }
  u7RootDisposition_commutes := by
    intro query obstruction audit same
    exact old.u7RootDisposition_commutes query obstruction audit
      ((compilation_audit old program inputs owners query _).symm.trans same)

theorem birthState_compiles_paid (query : old.Query)
    (paid : GeneratedStepAt (Idle.law (inputs query).input.environment (inputs query).input.expression)
      (initialEvent (inputs query)).state)
    (answered : (old.compileInquiry query).audit = .answered)
    (action : sourceAction old program (inputs query) = .inr paid) :
    (birthState old program inputs owners).compileInquiry query =
      .debtAdmission ((birthProgramAt old program inputs owners query paid action).generate
        (old.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt old.visit)) :=
  compilationAt_paid old program inputs owners query paid answered action _

theorem birth_root : (birthState old program inputs owners).root = old.root := rfl
theorem birth_visit : (birthState old program inputs owners).visit = old.visit := rfl
theorem birth_queries : (birthState old program inputs owners).Query = old.Query := rfl

end
end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
