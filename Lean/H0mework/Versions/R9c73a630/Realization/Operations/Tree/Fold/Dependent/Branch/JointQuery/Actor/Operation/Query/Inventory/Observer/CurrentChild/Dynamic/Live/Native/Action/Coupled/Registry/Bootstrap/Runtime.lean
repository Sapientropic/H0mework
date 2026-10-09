import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
namespace Bootstrap.Run
variable {S : Type u} {W X : S → Type u} [∀ slot,AddCommGroup (W slot)] {s : S}
variable (source : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=W) (Var:=X) (sort:=s))
variable (sourceCfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (scalar : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr (SourceOperationScalarInventoryLift.PairValue W) sourceCfg.LowVar s)))
variable (pair : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr (SourceOperationScalarInventoryLift.PairValue (SourceOperationScalarInventoryLift.PairValue W)) sourceCfg.LowVar s)))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=SourceOperationScalarInventoryLift.PairValue W) (PhysicalVar:=sourceCfg.LowVar) (sort:=s))
variable (strict : source.rank.1<(Bootstrap.initial source sourceCfg scalar pair).rank.1)

def presentationAt : Nat → RootInquiryStatePresentation
 | 0 => Bootstrap.presentation source sourceCfg scalar pair cfg
 | offset+1 => Registry.presentation (Bootstrap.frameAt source sourceCfg scalar pair cfg offset)
  cfg

def queryAt (count : Nat) : (presentationAt source sourceCfg scalar pair cfg count).Query := by
 cases count with
 | zero => exact Bootstrap.query source sourceCfg
 | succ offset =>
  exact Registry.query (Bootstrap.frameAt source sourceCfg scalar pair cfg offset)
   cfg

theorem query_unique (count : Nat) (candidate : (presentationAt source sourceCfg scalar pair cfg count).Query) :
 candidate=queryAt source sourceCfg scalar pair cfg count := by
 cases count with
 | zero =>
  exact Original.query_unique source
   sourceCfg candidate
 | succ offset =>
  exact Original.query_unique (Bootstrap.frameAt source sourceCfg scalar pair cfg offset)
   cfg candidate

def process : SourceNativeInquiryEngineProcess.{u} where
 State:=ULift.{u} Nat
 stateAt:=fun count => .active (presentationAt source sourceCfg scalar pair cfg count.down)
 erase_injective:=by
  intro ⟨first⟩ ⟨second⟩ firstState secondState firstActive secondActive same
  cases firstActive
  cases secondActive
  cases first with
  | zero =>
   cases second with
   | zero => rfl
   | succ offset => exact False.elim (Bootstrap.boot_tail_separated source sourceCfg scalar pair cfg strict offset same)
  | succ first =>
   cases second with
   | zero => exact False.elim (Bootstrap.boot_tail_separated source sourceCfg scalar pair cfg strict first same.symm)
   | succ second =>
    exact congrArg (fun count => ULift.up (count+1)) (Registry.frames_erase_injective
     (Bootstrap.initial source sourceCfg scalar pair)
     cfg same)
 initial:=.up 0
 successorAt:=fun ⟨count⟩ candidate => by
  cases count with
  | zero => exact ⟨.up 1,Bootstrap.successor_valid source sourceCfg scalar pair cfg candidate⟩
  | succ offset => exact ⟨.up (offset+2),Registry.successor_valid
     (Bootstrap.frameAt source sourceCfg scalar pair cfg offset)
     cfg candidate⟩

def nextQuery (count : (process source sourceCfg scalar pair cfg strict).State)
 (candidate : ((process source sourceCfg scalar pair cfg strict).stateAt count).Query) :
 ((process source sourceCfg scalar pair cfg strict).stateAt
  ((process source sourceCfg scalar pair cfg strict).successorAt count candidate).val).Query := by
 rcases count with ⟨count⟩
 cases count with
 | zero => exact queryAt source sourceCfg scalar pair cfg 1
 | succ offset => exact queryAt source sourceCfg scalar pair cfg (offset+2)

theorem nextQuery_unique (count : (process source sourceCfg scalar pair cfg strict).State)
 (candidate : ((process source sourceCfg scalar pair cfg strict).stateAt count).Query)
 (nextCandidate : ((process source sourceCfg scalar pair cfg strict).stateAt
  ((process source sourceCfg scalar pair cfg strict).successorAt count candidate).val).Query) :
 nextCandidate=nextQuery source sourceCfg scalar pair cfg strict count candidate := by
 rcases count with ⟨count⟩
 cases count with
 | zero => exact query_unique source sourceCfg scalar pair cfg 1 nextCandidate
 | succ offset => exact query_unique source sourceCfg scalar pair cfg (offset+2) nextCandidate

def runtime : SourceNativeInquiryRuntime (process source sourceCfg scalar pair cfg strict) where
 activationLaw:=Engine.SourceNativeInquiryActivationLaw.ofUnique
  (queryAt source sourceCfg scalar pair cfg 0)
  (query_unique source sourceCfg scalar pair cfg 0)
  (nextQuery source sourceCfg scalar pair cfg strict)
  (nextQuery_unique source sourceCfg scalar pair cfg strict)

private theorem next_node (count : Nat) (engine : Engine (process source sourceCfg scalar pair cfg strict))
 (same : engine.node=.active (presentationAt source sourceCfg scalar pair cfg count))
 (activation : Engine.SourceNativeInquiryActivationAt engine) :
 (engine.ask activation).next.node=.active (presentationAt source sourceCfg scalar pair cfg (count+1)) := by
 rcases engine with ⟨registered⟩
 have registeredEq : registered=ULift.up count := (process source sourceCfg scalar pair cfg strict).erase_injective rfl rfl
  (congrArg RootInquiryProcessNode.erase same)
 subst registered
 cases count <;> rfl

theorem actual_node (count : Nat) : ((runtime source sourceCfg scalar pair cfg strict).stateAt count).engine.node=
 .active (presentationAt source sourceCfg scalar pair cfg count) := by
 induction count with
 | zero => rfl
 | succ count prior =>
  exact next_node source sourceCfg scalar pair cfg strict count
   ((runtime source sourceCfg scalar pair cfg strict).stateAt count).engine prior
   ((runtime source sourceCfg scalar pair cfg strict).stateAt count).activation

theorem actual_next (count : Nat) : ((runtime source sourceCfg scalar pair cfg strict).tickAt count).next.node=
 .active (presentationAt source sourceCfg scalar pair cfg (count+1)) :=
 actual_node source sourceCfg scalar pair cfg strict (count+1)

private theorem query_at_node (count : Nat) (engine : Engine (process source sourceCfg scalar pair cfg strict))
 (same : engine.node=.active (presentationAt source sourceCfg scalar pair cfg count))
 (activation : Engine.SourceNativeInquiryActivationAt engine) :
 HEq activation.query (queryAt source sourceCfg scalar pair cfg count) := by
 rcases engine with ⟨registered⟩
 have registeredEq : registered=ULift.up count := (process source sourceCfg scalar pair cfg strict).erase_injective rfl rfl
  (congrArg RootInquiryProcessNode.erase same)
 subst registered
 exact heq_of_eq (query_unique source sourceCfg scalar pair cfg count activation.query)

theorem actual_query (count : Nat) : HEq
 ((runtime source sourceCfg scalar pair cfg strict).stateAt count).activation.query
 (queryAt source sourceCfg scalar pair cfg count) :=
 query_at_node source sourceCfg scalar pair cfg strict count
  ((runtime source sourceCfg scalar pair cfg strict).stateAt count).engine
  (actual_node source sourceCfg scalar pair cfg strict count)
  ((runtime source sourceCfg scalar pair cfg strict).stateAt count).activation

theorem actual_boot_target : ((runtime source sourceCfg scalar pair cfg strict).tickAt 0).next.node=
 .active (Bootstrap.targetPresentation source sourceCfg scalar pair cfg) :=
 actual_next source sourceCfg scalar pair cfg strict 0

theorem actual_boot_target_root : type_of% (heq_of_eq (Bootstrap.target_root source sourceCfg scalar pair cfg
  (Bootstrap.sourceEvent source sourceCfg)).symm) :=
 heq_of_eq (Bootstrap.target_root source sourceCfg scalar pair cfg
  (Bootstrap.sourceEvent source sourceCfg)).symm

theorem actual_boot_compilation : HEq
 ((runtime source sourceCfg scalar pair cfg strict).tickAt 0).resolution
 (InternalInquiryResolutionAt.debtAdmission (Bootstrap.generatedAction source sourceCfg scalar pair cfg) :
  InternalInquiryResolutionAt (Bootstrap.presentation source sourceCfg scalar pair cfg)
   (Bootstrap.query source sourceCfg)) :=
 heq_of_eq (RootInquiryProcessNode.active_debtAdmission_resolution_eq
  (Bootstrap.presentation source sourceCfg scalar pair cfg)
  (Bootstrap.query source sourceCfg)
  (Bootstrap.generatedAction source sourceCfg scalar pair cfg)
  (Bootstrap.compiles source sourceCfg scalar pair cfg))

theorem actual_boot_answer : HEq
 ((runtime source sourceCfg scalar pair cfg strict).tickAt 0).answer
 (Bootstrap.generatedAction source sourceCfg scalar pair cfg).answer :=
 RootInquiryProcessNode.active_answer_heq_debtAdmission
  (Bootstrap.presentation source sourceCfg scalar pair cfg)
  (Bootstrap.query source sourceCfg)
  (Bootstrap.generatedAction source sourceCfg scalar pair cfg)
  (Bootstrap.compiles source sourceCfg scalar pair cfg)

theorem boot_first_write_preserved : HEq
 (Bootstrap.generatedAction source sourceCfg scalar pair cfg).target.firstSuccessor
 (Bootstrap.originalTargetAt source sourceCfg scalar pair cfg
  (Bootstrap.sourceEvent source sourceCfg)).firstSuccessor := HEq.rfl
theorem actual_boot_first_write : ∃ generated : SourceGeneratedDebtAdmissionActualActionAt
 (Bootstrap.birthProgram source sourceCfg scalar pair cfg)
 (Bootstrap.sourceEvent source sourceCfg),
 HEq ((runtime source sourceCfg scalar pair cfg strict).tickAt 0).resolution
  (InternalInquiryResolutionAt.debtAdmission generated :
   InternalInquiryResolutionAt (Bootstrap.presentation source sourceCfg scalar pair cfg)
    (Bootstrap.query source sourceCfg)) ∧
 HEq ((runtime source sourceCfg scalar pair cfg strict).tickAt 0).answer generated.answer ∧
 HEq generated.target.firstSuccessor
  (Bootstrap.originalTargetAt source sourceCfg scalar pair cfg
   (Bootstrap.sourceEvent source sourceCfg)).firstSuccessor :=
 ⟨Bootstrap.generatedAction source sourceCfg scalar pair cfg,
  actual_boot_compilation source sourceCfg scalar pair cfg strict,
  actual_boot_answer source sourceCfg scalar pair cfg strict,
  boot_first_write_preserved source sourceCfg scalar pair cfg⟩
end Bootstrap.Run
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
