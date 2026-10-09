import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Engine
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily
variable {S : Type u} (W : S → Type u) [∀ t,AddCommGroup (W t)]
local instance familyRuntimeGroup (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable {W} {X : S → Type u} {s : S}
variable (factory : Factory W X s)
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)
def processWithSourceFamily : SourceNativeInquiryEngineProcess.{u} where
 State:=ULift.{u} Nat
 stateAt:=fun count => .active (presentationAt factory initial firstCfg language count.down)
 erase_injective:=by
  intro ⟨first⟩ ⟨second⟩ firstState secondState firstActive secondActive same
  cases firstActive
  cases secondActive
  exact congrArg ULift.up (erasure_injective factory initial firstCfg language same)
 initial:=.up 0
 successorAt:=fun ⟨count⟩ candidate => ⟨.up (count+1),successor_valid factory initial firstCfg language count candidate⟩

def nextQuery (count : (processWithSourceFamily factory initial firstCfg language).State)
 (candidate : ((processWithSourceFamily factory initial firstCfg language).stateAt count).Query) :
 ((processWithSourceFamily factory initial firstCfg language).stateAt ((processWithSourceFamily factory initial firstCfg language).successorAt count candidate).val).Query :=
 queryAt factory initial firstCfg language (count.down+1)

theorem nextQuery_unique (count : (processWithSourceFamily factory initial firstCfg language).State)
 (candidate : ((processWithSourceFamily factory initial firstCfg language).stateAt count).Query)
 (nextCandidate : ((processWithSourceFamily factory initial firstCfg language).stateAt ((processWithSourceFamily factory initial firstCfg language).successorAt count candidate).val).Query) :
 nextCandidate=nextQuery factory initial firstCfg language count candidate := query_unique factory initial firstCfg language (count.down+1) nextCandidate

def runtime : SourceNativeInquiryRuntime (processWithSourceFamily factory initial firstCfg language) where
 activationLaw:=Engine.SourceNativeInquiryActivationLaw.ofUnique
  (queryAt factory initial firstCfg language 0) (query_unique factory initial firstCfg language 0)
  (nextQuery factory initial firstCfg language) (nextQuery_unique factory initial firstCfg language)

private theorem next_node (count : Nat) (engine : Engine (processWithSourceFamily factory initial firstCfg language))
 (same : engine.node=.active (presentationAt factory initial firstCfg language count))
 (activation : Engine.SourceNativeInquiryActivationAt engine) :
 (engine.ask activation).next.node=.active (presentationAt factory initial firstCfg language (count+1)) := by
 rcases engine with ⟨registered⟩
 have registeredEq : registered=ULift.up count := (processWithSourceFamily factory initial firstCfg language).erase_injective rfl rfl
  (congrArg RootInquiryProcessNode.erase same)
 subst registered
 rfl

theorem actual_node (count : Nat) : ((runtime factory initial firstCfg language).stateAt count).engine.node=
 .active (presentationAt factory initial firstCfg language count) := by
 induction count with
 | zero => rfl
 | succ count prior =>
   exact next_node factory initial firstCfg language count
    ((runtime factory initial firstCfg language).stateAt count).engine prior ((runtime factory initial firstCfg language).stateAt count).activation

theorem actual_next (count : Nat) : ((runtime factory initial firstCfg language).tickAt count).next.node=
 .active (presentationAt factory initial firstCfg language (count+1)) := actual_node factory initial firstCfg language (count+1)

private theorem at_node (count : Nat) (engine : Engine (processWithSourceFamily factory initial firstCfg language))
 (same : engine.node=.active (presentationAt factory initial firstCfg language count))
 (activation : Engine.SourceNativeInquiryActivationAt engine) :
 HEq (engine.ask activation).resolution (InternalInquiryResolutionAt.debtAdmission (generated factory initial firstCfg language count) :
  InternalInquiryResolutionAt (presentationAt factory initial firstCfg language count) (queryAt factory initial firstCfg language count)) ∧
 HEq (engine.ask activation).answer (generated factory initial firstCfg language count).answer := by
 rcases engine with ⟨registered⟩
 have registeredEq : registered=ULift.up count := (processWithSourceFamily factory initial firstCfg language).erase_injective rfl rfl
  (congrArg RootInquiryProcessNode.erase same)
 subst registered
 have compileAll : ∀ candidate : (presentationAt factory initial firstCfg language count).Query,
  (presentationAt factory initial firstCfg language count).state.base.compileInquiry candidate=
   .debtAdmission (generated factory initial firstCfg language count) := by
  intro candidate
  cases query_unique factory initial firstCfg language count candidate
  exact Admission.compiles (frameAt factory initial firstCfg language count) (cfgAt factory initial firstCfg language count)
   (scalarAt factory initial firstCfg language count) (pairAt factory initial firstCfg language count) (nextCfg factory initial firstCfg language count)
 constructor
 · have dep : ∀ candidate : (presentationAt factory initial firstCfg language count).Query,
    candidate=queryAt factory initial firstCfg language count →
    HEq (InternalInquiryResolutionAt.debtAdmission (generated factory initial firstCfg language count) : InternalInquiryResolutionAt (presentationAt factory initial firstCfg language count) candidate)
     (InternalInquiryResolutionAt.debtAdmission (generated factory initial firstCfg language count) : InternalInquiryResolutionAt (presentationAt factory initial firstCfg language count) (queryAt factory initial firstCfg language count)) := by
    intro candidate sameQuery
    subst candidate
    rfl
   exact (heq_of_eq (RootInquiryProcessNode.active_debtAdmission_resolution_eq
    (presentationAt factory initial firstCfg language count) activation.query (generated factory initial firstCfg language count)
    (compileAll activation.query))).trans (dep activation.query (query_unique factory initial firstCfg language count activation.query))
 · exact RootInquiryProcessNode.active_answer_heq_debtAdmission
    (presentationAt factory initial firstCfg language count) activation.query (generated factory initial firstCfg language count)
    (compileAll activation.query)

theorem actual_receipt (count : Nat) : type_of% (at_node factory initial firstCfg language count
 ((runtime factory initial firstCfg language).stateAt count).engine (actual_node factory initial firstCfg language count)
 ((runtime factory initial firstCfg language).stateAt count).activation) :=
 at_node factory initial firstCfg language count ((runtime factory initial firstCfg language).stateAt count).engine
 (actual_node factory initial firstCfg language count) ((runtime factory initial firstCfg language).stateAt count).activation

theorem actual_whole (count : Nat) : type_of% (generated factory initial firstCfg language count).target.firstDestination_heq :=
 (generated factory initial firstCfg language count).target.firstDestination_heq
end Lower.SourceFamily
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
