import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Engine
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Stage
set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily
namespace Actual
export ActivationSource (presentationAt queryAt queryAt_unique successor_valid erasure_injective first_target_full
 first_native_full first_born_full firstReceiver firstProgramme firstReceipt firstSelected firstBorn secondPresentation)
end Actual
variable {S : Type u} (W : S → Type u) [∀ target, AddCommGroup (W target)]
local instance familyRuntimeGroup (n : Nat) (target : S) : AddCommGroup (Lower.Value W n target) := Lower.groups W n target
variable {W} {X : S → Type u} {s : S}
variable (factory : Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (firstCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : firstCfg.LowVar = X)

/-- The Nat is the actual macro tick. The source stage carries its own family grade. -/
def processWithSourceFamily : SourceNativeInquiryEngineProcess.{u} where
 State := ULift.{u} Nat
 stateAt := fun tick => .active (Actual.presentationAt factory initial firstCfg language tick.down)
 erase_injective := by
  intro ⟨first⟩ ⟨second⟩ firstState secondState firstActive secondActive same
  cases firstActive
  cases secondActive
  exact congrArg ULift.up (Actual.erasure_injective factory initial firstCfg language same)
 initial := .up 0
 successorAt := fun ⟨tick⟩ query => ⟨.up (tick+1),Actual.successor_valid factory initial firstCfg language tick query⟩

def nextQuery (tick : (processWithSourceFamily factory initial firstCfg language).State)
 (_query : ((processWithSourceFamily factory initial firstCfg language).stateAt tick).Query) :
 ((processWithSourceFamily factory initial firstCfg language).stateAt
  ((processWithSourceFamily factory initial firstCfg language).successorAt tick _query).1).Query :=
 Actual.queryAt factory initial firstCfg language (tick.down+1)

theorem nextQuery_unique (tick : (processWithSourceFamily factory initial firstCfg language).State)
 (query : ((processWithSourceFamily factory initial firstCfg language).stateAt tick).Query)
 (nextCandidate : ((processWithSourceFamily factory initial firstCfg language).stateAt
  ((processWithSourceFamily factory initial firstCfg language).successorAt tick query).1).Query) :
 nextCandidate = nextQuery factory initial firstCfg language tick query :=
 Actual.queryAt_unique factory initial firstCfg language (tick.down+1) nextCandidate

def runtime : SourceNativeInquiryRuntime (processWithSourceFamily factory initial firstCfg language) where
 activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique
  (Actual.queryAt factory initial firstCfg language 0) (Actual.queryAt_unique factory initial firstCfg language 0)
  (nextQuery factory initial firstCfg language) (nextQuery_unique factory initial firstCfg language)

private theorem next_node (tick : Nat) (engine : Engine (processWithSourceFamily factory initial firstCfg language))
 (same : engine.node = .active (Actual.presentationAt factory initial firstCfg language tick))
 (activation : Engine.SourceNativeInquiryActivationAt engine) :
 (engine.ask activation).next.node = .active (Actual.presentationAt factory initial firstCfg language (tick+1)) := by
 rcases engine with ⟨registered⟩
 have registeredEq : registered = ULift.up tick := (processWithSourceFamily factory initial firstCfg language).erase_injective
  rfl rfl (congrArg RootInquiryProcessNode.erase same)
 subst registered
 rfl

theorem actual_node (tick : Nat) : ((runtime factory initial firstCfg language).stateAt tick).engine.node =
 .active (Actual.presentationAt factory initial firstCfg language tick) := by
 induction tick with
 | zero => rfl
 | succ tick previous =>
  exact next_node factory initial firstCfg language tick
   ((runtime factory initial firstCfg language).stateAt tick).engine previous
   ((runtime factory initial firstCfg language).stateAt tick).activation

theorem actual_next (tick : Nat) : ((runtime factory initial firstCfg language).tickAt tick).next.node =
 .active (Actual.presentationAt factory initial firstCfg language (tick+1)) := actual_node factory initial firstCfg language (tick+1)

private theorem query_at_node (tick : Nat) (engine : Engine (processWithSourceFamily factory initial firstCfg language))
 (same : engine.node = .active (Actual.presentationAt factory initial firstCfg language tick))
 (activation : Engine.SourceNativeInquiryActivationAt engine) :
 HEq activation.query (Actual.queryAt factory initial firstCfg language tick) := by
 rcases engine with ⟨registered⟩
 have registeredEq : registered = ULift.up tick := (processWithSourceFamily factory initial firstCfg language).erase_injective
  rfl rfl (congrArg RootInquiryProcessNode.erase same)
 subst registered
 exact heq_of_eq (Actual.queryAt_unique factory initial firstCfg language tick activation.query)

theorem actual_query (tick : Nat) :
 HEq ((runtime factory initial firstCfg language).stateAt tick).activation.query
  (Actual.queryAt factory initial firstCfg language tick) :=
 query_at_node factory initial firstCfg language tick ((runtime factory initial firstCfg language).stateAt tick).engine
  (actual_node factory initial firstCfg language tick) ((runtime factory initial firstCfg language).stateAt tick).activation

/-- This readout keeps the actual branch-specific receipt; it does not assert admission at every tick. -/
theorem actual_receipt (tick : Nat) : type_of%
 (((runtime factory initial firstCfg language).tickAt tick).resolution_eq_generated) :=
 ((runtime factory initial firstCfg language).tickAt tick).resolution_eq_generated

def actual_branch_receipt (tick : Nat) := ((runtime factory initial firstCfg language).tickAt tick).receipt

theorem actual_whole (tick : Nat) : type_of%
 (((runtime factory initial firstCfg language).tickAt tick).next_preservesGeneratedLivingLaw) :=
 ((runtime factory initial firstCfg language).tickAt tick).next_preservesGeneratedLivingLaw

theorem actual_first_activation_full : ((runtime factory initial firstCfg language).tickAt 0).next.node =
 .active (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission.targetPresentation
  initial firstCfg (ActivationSource.scalar factory 0 (ActivationSource.firstData initial) firstCfg language)
  (ActivationSource.pair factory 0 (ActivationSource.firstData initial) firstCfg language)
  (Actual.firstProgramme factory initial firstCfg language)) :=
 (actual_next factory initial firstCfg language 0).trans (congrArg RootInquiryProcessNode.active
  (Actual.first_target_full factory initial firstCfg language))

theorem actual_first_native (offset : Nat)
 (within : offset ≤ (Actual.firstReceipt factory initial firstCfg language).1) :
 ((runtime factory initial firstCfg language).stateAt (1+offset)).engine.node =
 .active (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget.presentation
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames
   (Actual.firstReceiver factory initial firstCfg language) (Actual.firstProgramme factory initial firstCfg language) offset)
  (Actual.firstProgramme factory initial firstCfg language)) :=
 (actual_node factory initial firstCfg language _).trans (congrArg RootInquiryProcessNode.active
  (Actual.first_native_full factory initial firstCfg language offset within))

theorem actual_first_born :
 ((runtime factory initial firstCfg language).tickAt (1+(Actual.firstReceipt factory initial firstCfg language).1)).next.node =
 .active (Actual.secondPresentation factory initial firstCfg language) :=
 (actual_next factory initial firstCfg language _).trans (congrArg RootInquiryProcessNode.active
  (Actual.first_born_full factory initial firstCfg language))

end Lower.SourceFamily
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
