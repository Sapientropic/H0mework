import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Observation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
namespace StockTarget
variable {S : Type u} {W X : S → Type u} [∀ slot,AddCommGroup (W slot)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=W) (Var:=X) (sort:=s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
def face : SourceNativeRootSemanticFaceAt (StockObservation.root frame cfg) (StockObservation.visit frame cfg) where
 projection:=(Original.resultInstallation frame cfg).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl
def consumer : SourceNativeInquiryAnswerConsumerAt (root:=StockObservation.root frame cfg) (visit:=StockObservation.visit frame cfg) (Registry.query frame cfg)
 (ULift.up.{u+1,u} (Original.actualOccurrence frame)) (frame.currentState.entryAt PUnit.unit) (face frame cfg) where
 projection:=(Original.consumerInstallation frame cfg).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl
 project_heq:=HEq.rfl

/-- Restrict the actual same-value birth target to the installed complete stock read. -/
def targetAt (event : ExactTemporalCausalRootEventAt
    (StockObservation.root frame cfg).toAuthoritativeRoot.toLedgerRoot (StockObservation.visit frame cfg)) :
    SourceNativeDebtAdmissionActualActionTargetAt (StockObservation.root frame cfg)
      (StockObservation.visit frame cfg) event (frame.currentState.entryAt PUnit.unit)
      (StockObservation.authority frame cfg) :=
  Observation.Material.target (oldRoot := Shared.root frame cfg)
    (oldVisit := StockObservation.visit frame cfg) (oldEvent := event)
    (oldEntry := frame.currentState.entryAt PUnit.unit)
    (oldAuthority := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.authority frame cfg)
    (StockObservation.read frame) (noFaithful frame) (StockObservation.authority frame cfg)
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.targetAt frame cfg event)
    (StockObservation.read (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame cfg))
    (noFaithful (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame cfg))

def birthProgram : SourceNativeDebtAdmissionActualActionProgramAt (StockObservation.root frame cfg)
    (StockObservation.visit frame cfg) (frame.currentState.entryAt PUnit.unit)
    (StockObservation.authority frame cfg) where
  targetAt := targetAt frame cfg

theorem target_root (event) : (targetAt frame cfg event).targetRoot =
    StockObservation.root (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame cfg) cfg := rfl

set_option maxHeartbeats 600000 in
theorem target_current (event) : (targetAt frame cfg event).targetAnswerAndNext.nextCurrent =
    ⟨_,(StockObservation.root (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame cfg) cfg).toAuthoritativeRoot,
      StockObservation.visit (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame cfg) cfg⟩ := by
  have lifted := Observation.Material.target_next
    (oldRoot := Shared.root frame cfg)
    (oldVisit := StockObservation.visit frame cfg) (oldEvent := event)
    (oldEntry := frame.currentState.entryAt PUnit.unit)
    (oldAuthority := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.authority frame cfg)
    (StockObservation.read frame) (noFaithful frame) (StockObservation.authority frame cfg)
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.targetAt frame cfg event)
    (StockObservation.read (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame cfg))
    (noFaithful (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame cfg))
  exact lifted.trans (congrArg (fun current => Observation.Material.current current
    (StockObservation.read (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame cfg)))
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.target_next frame cfg event))

theorem original_first_successor (event) : HEq (targetAt frame cfg event).firstSuccessor
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.targetAt frame cfg event).firstSuccessor := HEq.rfl

def compilation (candidate : Germ frame cfg) : SourceNativeInquiryCompilationProgramAt (StockObservation.root frame cfg)
 (StockObservation.visit frame cfg) (Original.base frame).U7 (Original.base frame).calculus
 (StockObservation.root frame cfg).source.base.lawSurface candidate (ULift.up.{u+1,u} (Original.actualOccurrence frame))
 (frame.currentState.entryAt PUnit.unit) (StockObservation.authority frame cfg) where
 compile:=fun event => match frame.action with
  | .inr _ => .answered (face frame cfg) (by
      cases Original.query_unique frame cfg candidate
      exact consumer frame cfg)
  | .inl _ => .debtAdmission ((birthProgram frame cfg).generate event)

def state : RootInquiryStateAt (C.World frame.registered) (C.JointV frame.registered frame.packetAt) where
 root:=StockObservation.root frame cfg
 visit:=StockObservation.visit frame cfg
 U7:=(Original.base frame).U7
 calculus:=(Original.base frame).calculus
 Query:=Germ frame cfg
 entryAt:=fun _ => frame.currentState.entryAt PUnit.unit
 authorityAt:=fun _ => StockObservation.authority frame cfg
 compilationProgramAt:=compilation frame cfg
 compilationFaceAt:=fun candidate => by
  cases Original.query_unique frame cfg candidate
  refine { projection := (Original.compilationInstallation frame cfg).embed PUnit.unit
           active := PUnit.unit
           classifier_eq := rfl
           project_heq := ?_ }
  unfold compilation
  cases frame.action <;> exact HEq.rfl
 u7RootDisposition_commutes:=by
  intro candidate _ _ impossible
  cases Original.query_unique frame cfg candidate
  change (match frame.action with
    | .inr _ => SourceNativeInquiryCompilationAt.answered (face frame cfg) (consumer frame cfg)
    | .inl _ => SourceNativeInquiryCompilationAt.debtAdmission ((birthProgram frame cfg).generate
        ((StockObservation.root frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (StockObservation.visit frame cfg)))).audit = _ at impossible
  generalize frame.action = selected at impossible
  cases selected <;> exact nomatch impossible

def presentation : RootInquiryStatePresentation where
 N:=C.World frame.registered
 V:=C.JointV frame.registered frame.packetAt
 state:=.create (state frame cfg)
theorem at_depth : StockObservation.visit frame cfg=StockObservation.visitAt frame cfg (frame.depth+1) := rfl
theorem compiles_paid (paid : DebtActivationWorld.GeneratedStepAt
    (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment frame.registered.input.expression)
    frame.event.state) (actual : frame.action = .inr paid) :
    (state frame cfg).compileInquiry (Registry.query frame cfg) = .answered (face frame cfg) (consumer frame cfg) := by
  change (match frame.action with
    | .inr _ => SourceNativeInquiryCompilationAt.answered (face frame cfg) (consumer frame cfg)
    | .inl _ => SourceNativeInquiryCompilationAt.debtAdmission ((birthProgram frame cfg).generate _)) = _
  rw [actual]
  rfl

theorem compiles_settled (settled : SourceOperationExecutionDebt.Settlement frame.event.state)
    (actual : frame.action = .inl settled) :
    (state frame cfg).compileInquiry (Registry.query frame cfg) = .debtAdmission ((birthProgram frame cfg).generate
      ((StockObservation.root frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (StockObservation.visit frame cfg))) := by
  change (match frame.action with
    | .inr _ => SourceNativeInquiryCompilationAt.answered (face frame cfg) (consumer frame cfg)
    | .inl _ => SourceNativeInquiryCompilationAt.debtAdmission ((birthProgram frame cfg).generate _)) = _
  rw [actual]
  rfl

set_option maxHeartbeats 600000 in
theorem successor_valid (candidate : (presentation frame cfg).Query) :
    (presentation (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame cfg) cfg).erase =
      (RootInquiryProcessNode.answered (presentation frame cfg) candidate).erase ∧
    (.active (presentation frame cfg) : RootInquiryProcessNode).PreservesGeneratedLivingLawAt candidate
      (.active (presentation (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame cfg) cfg)) := by
  cases Original.query_unique frame cfg candidate
  cases actual : frame.action with
  | inr paid =>
      apply RootInquiryProcessNode.active_directlyAnswered_successor_valid
        (presentation frame cfg) (presentation (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame cfg) cfg)
        (Registry.query frame cfg) (face frame cfg) (consumer frame cfg) (compiles_paid frame cfg paid actual)
      · unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
        rw [actual]
        apply congrArg (fun current => (⟨_,current⟩ : AnyAuthoritativeRootCurrent.{u}))
        symm
        apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
        rfl
      · unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
        rw [actual]
        exact HEq.rfl
  | inl settled =>
      apply RootInquiryProcessNode.active_debtAdmission_successor_valid
        (presentation frame cfg) (presentation (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame cfg) cfg)
        (Registry.query frame cfg)
        ((birthProgram frame cfg).generate ((StockObservation.root frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (StockObservation.visit frame cfg)))
        (compiles_settled frame cfg settled actual)
      · unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
        rw [actual]
        apply congrArg (fun current => (⟨_,current⟩ : AnyAuthoritativeRootCurrent.{u}))
        exact (target_current frame cfg _).symm
      · unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
        rw [actual]
        change HEq (StockObservation.root
          (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame cfg) cfg)
          (targetAt frame cfg _).targetRoot
        exact heq_of_eq (target_root frame cfg _).symm

end StockTarget
namespace StockAdmission
variable {S : Type u} {W X : S → Type u} [∀ slot,AddCommGroup (W slot)] {s : S}
variable (source : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=W) (Var:=X) (sort:=s))
variable (sourceCfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (scalar : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (SourceOperationScalarInventoryLift.PairValue W) sourceCfg.LowVar s)))
variable (pair : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (SourceOperationScalarInventoryLift.PairValue (SourceOperationScalarInventoryLift.PairValue W)) sourceCfg.LowVar s)))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=SourceOperationScalarInventoryLift.PairValue W) (PhysicalVar:=sourceCfg.LowVar) (sort:=s))
abbrev sourceRoot:=StockObservation.root source
 sourceCfg
abbrev sourceVisit:=StockObservation.visit source
 sourceCfg
abbrev sourceAuthority:=StockObservation.authority source
 sourceCfg
abbrev query:=Registry.query source
 sourceCfg
abbrev entry:=source.currentState.entryAt PUnit.unit
abbrev Event:=ExactTemporalCausalRootEventAt (sourceRoot source sourceCfg).toAuthoritativeRoot.toLedgerRoot
 (sourceVisit source sourceCfg)

def targetAt (event : Event source sourceCfg) :
 SourceNativeDebtAdmissionActualActionTargetAt (sourceRoot source sourceCfg)
 (sourceVisit source sourceCfg) event (entry source) (sourceAuthority source sourceCfg) :=
 Observation.Material.target (oldRoot:=Shared.root source sourceCfg)
  (oldVisit:=sourceVisit source sourceCfg) (oldEvent:=event)
  (oldEntry:=entry source)
  (oldAuthority:=SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.authority source sourceCfg)
  (StockObservation.read source) (noFaithful source) (sourceAuthority source sourceCfg)
  (Bootstrap.originalTargetAt source sourceCfg scalar pair cfg event)
  (StockObservation.read (Bootstrap.initial source sourceCfg scalar pair))
  (noFaithful (Bootstrap.initial source sourceCfg scalar pair))

theorem target_root (event : Event source sourceCfg) :
 (targetAt source sourceCfg scalar pair cfg event).targetRoot=
 StockObservation.root (Bootstrap.initial source sourceCfg scalar pair) cfg :=
 congrArg (fun live : SourceNativeLivingRootClosure
  (C.World (Bootstrap.initial source sourceCfg scalar pair).registered)
  (C.JointV (Bootstrap.initial source sourceCfg scalar pair).registered (Bootstrap.initial source sourceCfg scalar pair).packetAt) => Observation.Material.root live.toAuthoritativeRoot
  (StockObservation.read (Bootstrap.initial source sourceCfg scalar pair))
  (noFaithful (Bootstrap.initial source sourceCfg scalar pair)))
 (Bootstrap.original_target_root source sourceCfg scalar pair cfg event)

def birthProgram : SourceNativeDebtAdmissionActualActionProgramAt (sourceRoot source sourceCfg)
 (sourceVisit source sourceCfg)
 (entry source) (sourceAuthority source sourceCfg) where
 targetAt:=targetAt source sourceCfg scalar pair cfg
abbrev sourceEvent:=(sourceRoot source sourceCfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
 (sourceVisit source sourceCfg)
abbrev generatedAction:=(birthProgram source sourceCfg scalar pair cfg).generate
 (sourceEvent source sourceCfg)

def compilation (candidate : Germ source
 sourceCfg) : SourceNativeInquiryCompilationProgramAt
 (sourceRoot source sourceCfg) (sourceVisit source sourceCfg)
 (Original.base source).U7
 (Original.base source).calculus
 (sourceRoot source sourceCfg).source.base.lawSurface candidate
 (ULift.up.{u+1,u} (Original.actualOccurrence source))
 (entry source) (sourceAuthority source sourceCfg) where
 compile:=fun event => by
  cases Original.query_unique source
   sourceCfg candidate
  exact .debtAdmission ((birthProgram source sourceCfg scalar pair cfg).generate event)

def state : RootInquiryStateAt
 (C.World source.registered)
 (C.JointV source.registered
  source.packetAt) where
 root:=sourceRoot source sourceCfg
 visit:=sourceVisit source sourceCfg
 U7:=(Original.base source).U7
 calculus:=(Original.base source).calculus
 Query:=Germ source sourceCfg
 entryAt:=fun _ => entry source
 authorityAt:=fun _ => sourceAuthority source sourceCfg
 compilationProgramAt:=compilation source sourceCfg scalar pair cfg
 compilationFaceAt:=fun candidate => by
  cases Original.query_unique source
   sourceCfg candidate
  exact {projection:=(Original.compilationInstallation source
           sourceCfg).embed PUnit.unit
         active:=PUnit.unit
         classifier_eq:=rfl
         project_heq:=HEq.rfl}
 u7RootDisposition_commutes:=by
  intro candidate _ _ impossible
  cases Original.query_unique source
   sourceCfg candidate
  exact nomatch impossible

def presentation : RootInquiryStatePresentation where
 N:=C.World source.registered
 V:=C.JointV source.registered
  source.packetAt
 state:=.create (state source sourceCfg scalar pair cfg)
abbrev targetPresentation:=StockTarget.presentation (Bootstrap.initial source sourceCfg scalar pair) cfg

theorem target_next (event : Event source sourceCfg) : type_of%
 ((targetAt source sourceCfg scalar pair cfg event).targetAnswerAndNext_next_eq) :=
 (targetAt source sourceCfg scalar pair cfg event).targetAnswerAndNext_next_eq

theorem canonical_target (event : Event source sourceCfg) : type_of%
 (Observation.canonical_next_congr (target_root source sourceCfg scalar pair cfg event)) :=
 Observation.canonical_next_congr (target_root source sourceCfg scalar pair cfg event)

theorem target_current (event : Event source sourceCfg) : type_of%
 ((canonical_target source sourceCfg scalar pair cfg event).trans
  (StockObservation.canonical_initial_next (Bootstrap.initial source sourceCfg scalar pair) cfg)) :=
 (canonical_target source sourceCfg scalar pair cfg event).trans
  (StockObservation.canonical_initial_next (Bootstrap.initial source sourceCfg scalar pair) cfg)

theorem compiles : (state source sourceCfg scalar pair cfg).compileInquiry
 (query source sourceCfg)=
 .debtAdmission (generatedAction source sourceCfg scalar pair cfg) := rfl

theorem initial_visit : type_of% (StockTarget.at_depth (Bootstrap.initial source sourceCfg scalar pair) cfg) :=
 StockTarget.at_depth _ _

theorem target_erasure : (targetPresentation source sourceCfg scalar pair cfg).erase=
 ⟨(generatedAction source sourceCfg scalar pair cfg).target.TargetN,
  (generatedAction source sourceCfg scalar pair cfg).target.targetAnswerAndNext.nextCurrent⟩ := by
 have generatedNext := target_current source sourceCfg scalar pair cfg (sourceEvent source sourceCfg)
 have typed : (targetAt source sourceCfg scalar pair cfg (sourceEvent source sourceCfg)).targetAnswerAndNext.nextCurrent=
  ⟨_,(StockObservation.root (Bootstrap.initial source sourceCfg scalar pair) cfg).toAuthoritativeRoot,
   StockObservation.visit (Bootstrap.initial source sourceCfg scalar pair) cfg⟩ := by
  change (targetAt source sourceCfg scalar pair cfg (sourceEvent source sourceCfg)).targetRoot.generatedNextCurrentAt
   (.finite (targetAt source sourceCfg scalar pair cfg (sourceEvent source sourceCfg)).targetRoot.toAuthoritativeRoot.toRoot.initialVisit)=_
  rw [initial_visit source sourceCfg scalar pair cfg]
  exact generatedNext
 exact (congrArg (fun current => (⟨(generatedAction source sourceCfg scalar pair cfg).target.TargetN,current⟩ : AnyAuthoritativeRootCurrent.{u})) typed).symm

theorem target_full_root : type_of% (heq_of_eq
 (target_root source sourceCfg scalar pair cfg (sourceEvent source sourceCfg)).symm) :=
 heq_of_eq (target_root source sourceCfg scalar pair cfg (sourceEvent source sourceCfg)).symm

theorem valid : type_of% (RootInquiryProcessNode.active_debtAdmission_successor_valid
 (presentation source sourceCfg scalar pair cfg)
 (targetPresentation source sourceCfg scalar pair cfg)
 (query source sourceCfg)
 (generatedAction source sourceCfg scalar pair cfg)
 (compiles source sourceCfg scalar pair cfg)
 (target_erasure source sourceCfg scalar pair cfg)
 (target_full_root source sourceCfg scalar pair cfg)) :=
 RootInquiryProcessNode.active_debtAdmission_successor_valid
 (presentation source sourceCfg scalar pair cfg)
 (targetPresentation source sourceCfg scalar pair cfg)
 (query source sourceCfg)
 (generatedAction source sourceCfg scalar pair cfg)
 (compiles source sourceCfg scalar pair cfg)
 (target_erasure source sourceCfg scalar pair cfg)
 (target_full_root source sourceCfg scalar pair cfg)
theorem successor_valid (candidate : (presentation source sourceCfg scalar pair cfg).Query) :
 (targetPresentation source sourceCfg scalar pair cfg).erase=
 (RootInquiryProcessNode.answered (presentation source sourceCfg scalar pair cfg) candidate).erase ∧
 (.active (presentation source sourceCfg scalar pair cfg) : RootInquiryProcessNode).PreservesGeneratedLivingLawAt
 candidate (.active (targetPresentation source sourceCfg scalar pair cfg)) := by
 cases Original.query_unique source sourceCfg candidate
 exact valid source sourceCfg scalar pair cfg

end StockAdmission
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
