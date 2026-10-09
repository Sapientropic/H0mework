import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Shape
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace Observation
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
namespace Material
def root (original : SourceNativeAuthoritativeRootClosure N V) (read : SourceNativeMaterialBox.{u})
 (terminalEmpty : (current : V.Current) → IsEmpty (V.FaithfulTerminalAt current)) : SourceNativeLivingRootClosure N V :=
 ({source:={original.source with observationAt:=fun {_current} _ => read}
   emitted:=original.emitted
   compiler_commutes:=original.compiler_commutes} : SourceNativeAuthoritativeRootClosure N V).toLivingWithoutFaithfulTerminal terminalEmpty
theorem ledger (original : SourceNativeAuthoritativeRootClosure N V) (read : SourceNativeMaterialBox.{u})
 (terminalEmpty : (current : V.Current) → IsEmpty (V.FaithfulTerminalAt current)) :
 (root original read terminalEmpty).toAuthoritativeRoot.toLedgerRoot=original.toLedgerRoot := rfl
def current (original : SourceNativeAuthoritativeRootCurrentAt N) (read : SourceNativeMaterialBox.{u}) : SourceNativeAuthoritativeRootCurrentAt N :=
 ⟨original.V,
  {source:={original.root.source with observationAt:=fun {_current} _ => read}
   emitted:=original.root.emitted
   compiler_commutes:=original.root.compiler_commutes},original.visit⟩
end Material

abbrev root (original : SourceNativeAuthoritativeRootClosure N V) (ast : Shape)
 (terminalEmpty : (current : V.Current) → IsEmpty (V.FaithfulTerminalAt current)) :=
 Material.root original ⟨ULift.{u} Shape,ULift.up ast⟩ terminalEmpty

abbrev current (original : SourceNativeAuthoritativeRootCurrentAt N) (ast : Shape) :=
 Material.current original ⟨ULift.{u} Shape,ULift.up ast⟩

theorem ledger (original : SourceNativeAuthoritativeRootClosure N V) (ast : Shape)
 (terminalEmpty : (current : V.Current) → IsEmpty (V.FaithfulTerminalAt current)) :
 (root original ast terminalEmpty).toAuthoritativeRoot.toLedgerRoot=original.toLedgerRoot := rfl

private theorem generated_next (live : SourceNativeLivingRootClosure N V)
 (currentVisit : SourceNativeTemporalVisitAt live.toAuthoritativeRoot.toLedgerRoot)
 (successor : SourceNativeLedgerGeneratedSuccessorAt (live.emitted currentVisit.current)
  (live.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt currentVisit.current)) :
 live.generatedNextCurrentAt currentVisit=⟨V,live.toAuthoritativeRoot,currentVisit.next successor.next_eq⟩ := by
 generalize same : live.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt currentVisit.current=generated at successor ⊢
 cases generated with
 | nativeWrite write structural destination evolution =>
  exact live.generatedNextCurrentAt_eq_nativeWriteBranch currentVisit write structural destination evolution same successor.next_eq
 | relationWrite write structural destination evolution =>
  exact live.generatedNextCurrentAt_eq_relationWriteBranch currentVisit write structural destination evolution same successor.next_eq
 | continuedTransport write structural destination evolution =>
  exact live.generatedNextCurrentAt_eq_continuedTransportBranch currentVisit write structural destination evolution same successor.next_eq
 | borromeanRedirect write structural destination evolution =>
  exact live.generatedNextCurrentAt_eq_borromeanRedirectBranch currentVisit write structural destination evolution same successor.next_eq
 | faithfulTerminal terminal structural evolution => exact nomatch successor
namespace Material
variable {oldRoot : SourceNativeLivingRootClosure N V}
variable {oldVisit : SourceNativeTemporalVisitAt oldRoot.toAuthoritativeRoot.toLedgerRoot}
variable {oldEvent : ExactTemporalCausalRootEventAt oldRoot.toAuthoritativeRoot.toLedgerRoot oldVisit}
variable {oldEntry : OpenResponsibilityAt N
 (oldRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (oldRoot.emitted oldVisit.current))}
variable {oldAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt oldRoot oldVisit oldEntry}
variable (sourceRead : SourceNativeMaterialBox.{u})
variable (sourceEmpty : (current : V.Current) → IsEmpty (V.FaithfulTerminalAt current))
variable (sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
 (root oldRoot.toAuthoritativeRoot sourceRead sourceEmpty) oldVisit oldEntry)
variable (original : SourceNativeDebtAdmissionActualActionTargetAt oldRoot oldVisit oldEvent oldEntry oldAuthority)
variable (targetRead : SourceNativeMaterialBox.{u})
variable (targetEmpty : (current : original.TargetV.Current) → IsEmpty (original.TargetV.FaithfulTerminalAt current))
-- This transporter consumes the actual complete descriptor; both public reads
-- are installed before its emitter, while every ledger/projection field persists.
def target : SourceNativeDebtAdmissionActualActionTargetAt
 (root oldRoot.toAuthoritativeRoot sourceRead sourceEmpty) oldVisit oldEvent oldEntry sourceAuthority where
 law:=original.law
 sourceState:=original.sourceState
 stepEvent:=original.stepEvent
 sourceSuccessor:=original.sourceSuccessor
 TargetV:=original.TargetV
 targetRoot:=root original.targetRoot.toAuthoritativeRoot targetRead targetEmpty
 initialSupport_eq:=original.initialSupport_eq
 initialOldRow:=original.initialOldRow
 initialBornRow:=original.initialBornRow
 firstSuccessor:=original.firstSuccessor
 firstSupport_eq:=original.firstSupport_eq
 firstDestination_heq:=original.firstDestination_heq
 oldProjection:=original.oldProjection
 oldProjection_injective:=original.oldProjection_injective
 oldOutcome_heq:=original.oldOutcome_heq
 canonical_targetNextVisit_eq:=generated_next
  (root original.targetRoot.toAuthoritativeRoot targetRead targetEmpty)
  (.finite (root original.targetRoot.toAuthoritativeRoot targetRead targetEmpty).toAuthoritativeRoot.toRoot.initialVisit)
  original.firstSuccessor
 Answer:=original.Answer
 answer:=original.answer
 Receipt:=original.Receipt
 receipt:=original.receipt
theorem target_visit : (target sourceRead sourceEmpty sourceAuthority original targetRead targetEmpty).targetVisit=original.targetVisit := rfl
theorem target_next : (target sourceRead sourceEmpty sourceAuthority original targetRead targetEmpty).targetAnswerAndNext.nextCurrent=
 current original.targetAnswerAndNext.nextCurrent targetRead := by
 rw [(target sourceRead sourceEmpty sourceAuthority original targetRead targetEmpty).targetAnswerAndNext_next_eq,
  original.targetAnswerAndNext_next_eq]
 rfl
end Material

abbrev target {oldRoot : SourceNativeLivingRootClosure N V}
 {oldVisit : SourceNativeTemporalVisitAt oldRoot.toAuthoritativeRoot.toLedgerRoot}
 {oldEvent : ExactTemporalCausalRootEventAt oldRoot.toAuthoritativeRoot.toLedgerRoot oldVisit}
 {oldEntry : OpenResponsibilityAt N (oldRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (oldRoot.emitted oldVisit.current))}
 {oldAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt oldRoot oldVisit oldEntry}
 (sourceSyntax : Shape)
 (sourceEmpty : (current : V.Current) → IsEmpty (V.FaithfulTerminalAt current))
 (sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (root oldRoot.toAuthoritativeRoot sourceSyntax sourceEmpty) oldVisit oldEntry)
 (original : SourceNativeDebtAdmissionActualActionTargetAt oldRoot oldVisit oldEvent oldEntry oldAuthority)
 (targetSyntax : Shape)
 (targetEmpty : (current : original.TargetV.Current) → IsEmpty (original.TargetV.FaithfulTerminalAt current)) :=
 Material.target ⟨ULift.{u} Shape,ULift.up sourceSyntax⟩ sourceEmpty sourceAuthority original
  ⟨ULift.{u} Shape,ULift.up targetSyntax⟩ targetEmpty

variable {oldRoot : SourceNativeLivingRootClosure N V}
variable {oldVisit : SourceNativeTemporalVisitAt oldRoot.toAuthoritativeRoot.toLedgerRoot}
variable {oldEvent : ExactTemporalCausalRootEventAt oldRoot.toAuthoritativeRoot.toLedgerRoot oldVisit}
variable {oldEntry : OpenResponsibilityAt N
 (oldRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (oldRoot.emitted oldVisit.current))}
variable {oldAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt oldRoot oldVisit oldEntry}
variable (sourceSyntax : Shape)
variable (sourceEmpty : (current : V.Current) → IsEmpty (V.FaithfulTerminalAt current))
variable (sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
 (root oldRoot.toAuthoritativeRoot sourceSyntax sourceEmpty) oldVisit oldEntry)
variable (original : SourceNativeDebtAdmissionActualActionTargetAt oldRoot oldVisit oldEvent oldEntry oldAuthority)
variable (targetSyntax : Shape)
variable (targetEmpty : (current : original.TargetV.Current) → IsEmpty (original.TargetV.FaithfulTerminalAt current))
theorem target_visit : (target sourceSyntax sourceEmpty sourceAuthority original targetSyntax targetEmpty).targetVisit=original.targetVisit := rfl
theorem target_next : (target sourceSyntax sourceEmpty sourceAuthority original targetSyntax targetEmpty).targetAnswerAndNext.nextCurrent=
 current original.targetAnswerAndNext.nextCurrent targetSyntax := by
 rw [(target sourceSyntax sourceEmpty sourceAuthority original targetSyntax targetEmpty).targetAnswerAndNext_next_eq,
  original.targetAnswerAndNext_next_eq]
 rfl
end Observation
variable {S : Type u} {Value Var : S → Type u} [∀ s,AddCommGroup (Value s)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=s))
namespace Original
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (next nextBorn targetAt target_root target_next frames frames_forward)
end Original

theorem observed_root : Observation.root (Shared.root frame cfg).toAuthoritativeRoot
 (shape frame.rawRead.expression) (noFaithful frame)=observedRoot frame cfg := rfl

def targetAt (event : ExactTemporalCausalRootEventAt (observedRoot frame cfg).toAuthoritativeRoot.toLedgerRoot (visit frame cfg)) :
 SourceNativeDebtAdmissionActualActionTargetAt (observedRoot frame cfg) (visit frame cfg) event
 (frame.currentState.entryAt PUnit.unit) (authority frame cfg) :=
 Observation.target (oldRoot:=Shared.root frame cfg) (oldVisit:=visit frame cfg) (oldEvent:=event)
  (oldEntry:=frame.currentState.entryAt PUnit.unit)
  (oldAuthority:=SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.authority frame cfg)
  (shape frame.rawRead.expression) (noFaithful frame) (authority frame cfg)
  (Original.targetAt frame cfg event) (shape (Original.nextBorn frame cfg).rawRead.expression) (noFaithful (Original.nextBorn frame cfg))

theorem target_root (event : ExactTemporalCausalRootEventAt (observedRoot frame cfg).toAuthoritativeRoot.toLedgerRoot (visit frame cfg)) :
 (targetAt frame cfg event).targetRoot=observedRoot (Original.nextBorn frame cfg) cfg := by
 change Observation.root (Original.targetAt frame cfg event).targetRoot.toAuthoritativeRoot
  (shape (Original.nextBorn frame cfg).rawRead.expression) _=_
 rw [Original.target_root frame cfg event]
 rfl

def birthProgram : SourceNativeDebtAdmissionActualActionProgramAt (observedRoot frame cfg) (visit frame cfg)
 (frame.currentState.entryAt PUnit.unit) (authority frame cfg) where
 targetAt:=targetAt frame cfg

def compilation (candidate : Germ frame cfg) : SourceNativeInquiryCompilationProgramAt
 (observedRoot frame cfg) (visit frame cfg) (Original.base frame).U7 (Original.base frame).calculus
 (observedRoot frame cfg).source.base.lawSurface candidate (ULift.up.{u+1,u} (Original.actualOccurrence frame))
 (frame.currentState.entryAt PUnit.unit) (authority frame cfg) where
 compile:=fun event => match frame.action with
  | .inr _ => .answered (resultFace frame cfg) (by cases Original.query_unique frame cfg candidate; exact consumer frame cfg)
  | .inl _ => .debtAdmission ((birthProgram frame cfg).generate event)

theorem compilation_audit (candidate : Germ frame cfg) : (compilation frame cfg candidate).generate.output.audit=.answered := by
 cases Original.query_unique frame cfg candidate
 change (match frame.action with
  | .inr _ => SourceNativeInquiryCompilationAt.answered (resultFace frame cfg) (consumer frame cfg)
  | .inl _ => SourceNativeInquiryCompilationAt.debtAdmission ((birthProgram frame cfg).generate _)).audit=_
 cases frame.action <;> rfl

def state : RootInquiryStateAt (C.World frame.registered) (C.JointV frame.registered frame.packetAt) where
 root:=observedRoot frame cfg
 visit:=visit frame cfg
 U7:=(Original.base frame).U7
 calculus:=(Original.base frame).calculus
 Query:=Germ frame cfg
 entryAt:=fun _ => frame.currentState.entryAt PUnit.unit
 authorityAt:=fun _ => authority frame cfg
 compilationProgramAt:=compilation frame cfg
 compilationFaceAt:=fun candidate => by
  cases Original.query_unique frame cfg candidate
  refine {projection:=(Original.compilationInstallation frame cfg).embed PUnit.unit
          active:=PUnit.unit
          classifier_eq:=rfl
          project_heq:=?_}
  change HEq _ (SourceNativeInquiryCompilationTokenAt.canonical ((compilation frame cfg (query frame cfg)).generate.output.answerReadout))
  unfold compilation
  cases frame.action <;> exact HEq.rfl
 u7RootDisposition_commutes:=by
  intro candidate _ _ impossible
  have contrad:=(compilation_audit frame cfg candidate).symm.trans impossible
  exact nomatch contrad

def presentation : RootInquiryStatePresentation where
 N:=C.World frame.registered
 V:=C.JointV frame.registered frame.packetAt
 state:=.create (state frame cfg)

theorem presentation_current : (presentation frame cfg).erase=shapeCurrent frame cfg := rfl

theorem compiles_paid (paid : DebtActivationWorld.GeneratedStepAt
 (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment frame.registered.input.expression)
 frame.event.state) (actual : frame.action=.inr paid) :
 (state frame cfg).compileInquiry (query frame cfg)=.answered (resultFace frame cfg) (consumer frame cfg) := by
 change (match frame.action with
  | .inr _ => SourceNativeInquiryCompilationAt.answered (resultFace frame cfg) (consumer frame cfg)
  | .inl _ => SourceNativeInquiryCompilationAt.debtAdmission ((birthProgram frame cfg).generate _))=_
 rw [actual]
 rfl

theorem compiles_settled (settled : SourceOperationExecutionDebt.Settlement frame.event.state)
 (actual : frame.action=.inl settled) : (state frame cfg).compileInquiry (query frame cfg)=
 .debtAdmission ((birthProgram frame cfg).generate ((observedRoot frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (visit frame cfg))) := by
 change (match frame.action with
  | .inr _ => SourceNativeInquiryCompilationAt.answered (resultFace frame cfg) (consumer frame cfg)
  | .inl _ => SourceNativeInquiryCompilationAt.debtAdmission ((birthProgram frame cfg).generate _))=_
 rw [actual]
 rfl

theorem target_next (event : ExactTemporalCausalRootEventAt (observedRoot frame cfg).toAuthoritativeRoot.toLedgerRoot (visit frame cfg)) :
 (targetAt frame cfg event).targetAnswerAndNext.nextCurrent=
 ⟨_,(observedRoot (Original.nextBorn frame cfg) cfg).toAuthoritativeRoot,visit (Original.nextBorn frame cfg) cfg⟩ :=
 (Observation.target_next (oldRoot:=Shared.root frame cfg) (oldVisit:=visit frame cfg) (oldEvent:=event)
  (oldEntry:=frame.currentState.entryAt PUnit.unit)
  (oldAuthority:=SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.authority frame cfg)
  (shape frame.rawRead.expression) (noFaithful frame) (authority frame cfg)
  (Original.targetAt frame cfg event) (shape (Original.nextBorn frame cfg).rawRead.expression) (noFaithful (Original.nextBorn frame cfg))).trans
 (congrArg (fun next => Observation.current next (shape (Original.nextBorn frame cfg).rawRead.expression)) (Original.target_next frame cfg event))

theorem successor_valid (candidate : (presentation frame cfg).Query) :
 (presentation (Original.next frame cfg) cfg).erase=(RootInquiryProcessNode.answered (presentation frame cfg) candidate).erase ∧
 (.active (presentation frame cfg) : RootInquiryProcessNode).PreservesGeneratedLivingLawAt
 candidate (.active (presentation (Original.next frame cfg) cfg)) := by
 cases Original.query_unique frame cfg candidate
 cases actual : frame.action with
 | inr paid =>
  apply RootInquiryProcessNode.active_directlyAnswered_successor_valid
   (presentation frame cfg) (presentation (Original.next frame cfg) cfg) (query frame cfg)
   (resultFace frame cfg) (consumer frame cfg) (compiles_paid frame cfg paid actual)
  · unfold Original.next
    rw [actual]
    apply congrArg (fun current => (⟨_,current⟩ : AnyAuthoritativeRootCurrent.{u}))
    symm
    apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
    rfl
  · unfold Original.next
    rw [actual]
    exact HEq.rfl
 | inl settled =>
  apply RootInquiryProcessNode.active_debtAdmission_successor_valid
   (presentation frame cfg) (presentation (Original.next frame cfg) cfg) (query frame cfg)
   ((birthProgram frame cfg).generate ((observedRoot frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (visit frame cfg)))
   (compiles_settled frame cfg settled actual)
  · unfold Original.next
    rw [actual]
    apply congrArg (fun current => (⟨_,current⟩ : AnyAuthoritativeRootCurrent.{u}))
    exact (target_next frame cfg _).symm
  · unfold Original.next
    rw [actual]
    exact heq_of_eq (target_root frame cfg _).symm

theorem frames_erase_injective : Function.Injective
 (fun count => (presentation (Original.frames frame cfg count) cfg).erase) := by
 intro first second same
 have fees:=heterogeneous_fee (Original.frames frame cfg first) cfg (Original.frames frame cfg second) cfg same
 have ranks : (Original.frames frame cfg first).rank=(Original.frames frame cfg second).rank := Prod.ext fees
  ((current_depth _ cfg).symm.trans ((congrArg RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.erasedDepth same).trans (current_depth _ cfg)))
 rcases lt_trichotomy first second with less | equal | greater
 · obtain ⟨distance,index⟩:=Nat.exists_eq_add_of_lt less
   have progress:=Original.frames_forward frame cfg first distance
   rw [←index,ranks] at progress
   exact False.elim (RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.before_irrefl _ progress)
 · exact equal
 · obtain ⟨distance,index⟩:=Nat.exists_eq_add_of_lt greater
   have progress:=Original.frames_forward frame cfg second distance
   rw [←index,ranks] at progress
   exact False.elim (RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.before_irrefl _ progress)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
