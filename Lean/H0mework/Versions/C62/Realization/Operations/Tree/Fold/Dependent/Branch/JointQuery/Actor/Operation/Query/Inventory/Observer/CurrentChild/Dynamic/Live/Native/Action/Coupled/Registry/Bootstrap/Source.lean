import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
namespace Act
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
 (LowValue LowVar sort)
end Act
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (datum queryLaw resultLaw consumerLaw compilationLaw frames)
end Shared
namespace InitialVisit
variable {S : Type u} {W X : S → Type u} [∀ slot,AddCommGroup (W slot)] {s : S}
variable (f : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=W) (Var:=X) (sort:=s))
variable (c : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
theorem at_depth : Registry.visit f c=Registry.visitAt f c (f.depth+1) := rfl
end InitialVisit
namespace Bootstrap
section
variable {S : Type u} {W X : S → Type u} [∀ slot,AddCommGroup (W slot)] {s : S}
variable (source : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=W) (Var:=X) (sort:=s))
variable (sourceCfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (scalar : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr (SourceOperationScalarInventoryLift.PairValue W) sourceCfg.LowVar s)))
variable (pair : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr (SourceOperationScalarInventoryLift.PairValue (SourceOperationScalarInventoryLift.PairValue W)) sourceCfg.LowVar s)))
abbrev frame:=source
abbrev programme:=sourceCfg
def initial := {SourceGeneratedInquiryReceiptAction.Configured.lowInitial source sourceCfg with inventory:=some scalar,pairInventory:=some pair}
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=SourceOperationScalarInventoryLift.PairValue W) (PhysicalVar:=sourceCfg.LowVar) (sort:=s))
abbrev frameAt := Shared.frames (initial source sourceCfg scalar pair) cfg
def originalTargetAt (event : SourceGeneratedInquiryReceiptAction.Configured.Event source sourceCfg) : type_of%
 ((SourceGeneratedInquiryReceiptAction.birthProgram (source)
  (sourceCfg)).targetAt event) :=
 let initial := initial source sourceCfg scalar pair
 let original := (SourceGeneratedInquiryReceiptAction.birthProgram
  (source)
  (sourceCfg)).targetAt event
 let material := SourceOperationInquiry.Context.Faces.Execution.Activation.targetCoface original (SourceOperationInquiry.Context.Installation.component (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch initial))
 let configured := SourceOperationInquiry.Context.Faces.Execution.Activation.optionalTargetCoface material (Shared.datum initial cfg).component
 let withQuery := SourceOperationInquiry.Context.Faces.Execution.Activation.targetCoface configured (Shared.queryLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch initial) cfg)
 let withResult := SourceOperationInquiry.Context.Faces.Execution.Activation.targetCoface withQuery (Shared.resultLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch initial) cfg)
 let withConsumer := SourceOperationInquiry.Context.Faces.Execution.Activation.targetCoface withResult (Shared.consumerLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch initial) cfg)
 SourceOperationInquiry.Context.Faces.Execution.Activation.targetCoface withConsumer (Shared.compilationLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch initial) cfg)
theorem original_target_root (event : SourceGeneratedInquiryReceiptAction.Configured.Event source sourceCfg) :
 (originalTargetAt source sourceCfg scalar pair cfg event).targetRoot=
 Shared.root (initial source sourceCfg scalar pair) cfg := rfl
abbrev sourceRoot:=observedRoot (frame source)
 (programme sourceCfg)
abbrev sourceVisit:=Registry.visit (frame source)
 (programme sourceCfg)
abbrev sourceAuthority:=Registry.authority (frame source)
 (programme sourceCfg)
abbrev query:=Registry.query (frame source)
 (programme sourceCfg)
abbrev entry:=(frame source).currentState.entryAt PUnit.unit
abbrev Event:=ExactTemporalCausalRootEventAt (sourceRoot source sourceCfg).toAuthoritativeRoot.toLedgerRoot
 (sourceVisit source sourceCfg)

def targetAt (event : Event source sourceCfg) :
 SourceNativeDebtAdmissionActualActionTargetAt (sourceRoot source sourceCfg)
 (sourceVisit source sourceCfg) event
 (entry source) (sourceAuthority source sourceCfg) :=
 Observation.target (oldRoot:=Shared.root (frame source)
   (programme sourceCfg))
  (oldVisit:=sourceVisit source sourceCfg) (oldEvent:=event)
  (oldEntry:=entry source)
  (oldAuthority:=SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.authority
   (frame source) (programme sourceCfg))
  (shape (frame source).rawRead.expression)
  (noFaithful (frame source))
  (sourceAuthority source sourceCfg)
  (originalTargetAt source sourceCfg scalar pair cfg event)
  (shape (initial source sourceCfg scalar pair).rawRead.expression)
  (noFaithful (initial source sourceCfg scalar pair))

theorem target_root (event : Event source sourceCfg) :
 (targetAt source sourceCfg scalar pair cfg event).targetRoot=
 observedRoot (initial source sourceCfg scalar pair)
  cfg :=
 Observation.root_congr (original_target_root source sourceCfg scalar pair cfg event)
  (shape (initial source sourceCfg scalar pair).rawRead.expression)
  (noFaithful (initial source sourceCfg scalar pair))

def birthProgram : SourceNativeDebtAdmissionActualActionProgramAt (sourceRoot source sourceCfg)
 (sourceVisit source sourceCfg)
 (entry source) (sourceAuthority source sourceCfg) where
 targetAt:=targetAt source sourceCfg scalar pair cfg
abbrev sourceEvent:=(sourceRoot source sourceCfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
 (sourceVisit source sourceCfg)
abbrev generatedAction:=(birthProgram source sourceCfg scalar pair cfg).generate
 (sourceEvent source sourceCfg)

def compilation (candidate : Germ (frame source)
 (programme sourceCfg)) : SourceNativeInquiryCompilationProgramAt
 (sourceRoot source sourceCfg) (sourceVisit source sourceCfg)
 (Original.base source).U7
 (Original.base source).calculus
 (sourceRoot source sourceCfg).source.base.lawSurface candidate
 (ULift.up.{u+1,u} (Original.actualOccurrence source))
 (entry source) (sourceAuthority source sourceCfg) where
 compile:=fun event => by
  cases Original.query_unique (frame source)
   (programme sourceCfg) candidate
  exact .debtAdmission ((birthProgram source sourceCfg scalar pair cfg).generate event)

def state : RootInquiryStateAt
 (C.World (frame source).registered)
 (C.JointV (frame source).registered
  (frame source).packetAt) where
 root:=sourceRoot source sourceCfg
 visit:=sourceVisit source sourceCfg
 U7:=(Original.base source).U7
 calculus:=(Original.base source).calculus
 Query:=Germ (frame source) (programme sourceCfg)
 entryAt:=fun _ => entry source
 authorityAt:=fun _ => sourceAuthority source sourceCfg
 compilationProgramAt:=compilation source sourceCfg scalar pair cfg
 compilationFaceAt:=fun candidate => by
  cases Original.query_unique (frame source)
   (programme sourceCfg) candidate
  exact {projection:=(Original.compilationInstallation (frame source)
           (programme sourceCfg)).embed PUnit.unit
         active:=PUnit.unit
         classifier_eq:=rfl
         project_heq:=HEq.rfl}
 u7RootDisposition_commutes:=by
  intro candidate _ _ impossible
  cases Original.query_unique (frame source)
   (programme sourceCfg) candidate
  exact nomatch impossible

def presentation : RootInquiryStatePresentation where
 N:=C.World (frame source).registered
 V:=C.JointV (frame source).registered
  (frame source).packetAt
 state:=.create (state source sourceCfg scalar pair cfg)
abbrev targetPresentation:=Registry.presentation (initial source sourceCfg scalar pair)
 cfg

theorem target_next (event : Event source sourceCfg) : type_of%
 ((targetAt source sourceCfg scalar pair cfg event).targetAnswerAndNext_next_eq) :=
 (targetAt source sourceCfg scalar pair cfg event).targetAnswerAndNext_next_eq

theorem canonical_target (event : Event source sourceCfg) : type_of%
 (Observation.canonical_next_congr (target_root source sourceCfg scalar pair cfg event)) :=
 Observation.canonical_next_congr (target_root source sourceCfg scalar pair cfg event)

theorem target_current (event : Event source sourceCfg) : type_of%
 ((canonical_target source sourceCfg scalar pair cfg event).trans
  (canonical_initial_next (initial source sourceCfg scalar pair) cfg)) :=
 (canonical_target source sourceCfg scalar pair cfg event).trans
  (canonical_initial_next (initial source sourceCfg scalar pair) cfg)

theorem compiles : (state source sourceCfg scalar pair cfg).compileInquiry
 (query source sourceCfg)=
 .debtAdmission (generatedAction source sourceCfg scalar pair cfg) := rfl

theorem initial_visit : type_of% (InitialVisit.at_depth (initial source sourceCfg scalar pair) cfg) :=
 InitialVisit.at_depth _ _

theorem target_erasure : (targetPresentation source sourceCfg scalar pair cfg).erase=
 ⟨(generatedAction source sourceCfg scalar pair cfg).target.TargetN,
  (generatedAction source sourceCfg scalar pair cfg).target.targetAnswerAndNext.nextCurrent⟩ := by
 have generatedNext := target_current source sourceCfg scalar pair cfg (sourceEvent source sourceCfg)
 have typed : (targetAt source sourceCfg scalar pair cfg (sourceEvent source sourceCfg)).targetAnswerAndNext.nextCurrent=
  ⟨_,(observedRoot (initial source sourceCfg scalar pair) cfg).toAuthoritativeRoot,
   Registry.visit (initial source sourceCfg scalar pair) cfg⟩ := by
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

theorem boot_tail_separated (strict : source.rank.1<(initial source sourceCfg scalar pair).rank.1) (offset : Nat) :
 (presentation source sourceCfg scalar pair cfg).erase≠
 (Registry.presentation (frameAt source sourceCfg scalar pair cfg offset) cfg).erase :=
 first_tail_separated source sourceCfg (initial source sourceCfg scalar pair) cfg strict offset

end
end Bootstrap
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
