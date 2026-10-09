import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Runtime
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Raw
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationScalarInventoryLift
namespace C
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Activated
 (source sourceCfg scalar pair cfg strict runtime frameAt presentationAt actual_node)
end C
namespace I
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Installed (sourceCfg)
end I
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Lower (installation liftedRaw)
end L
namespace Act
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
 (PhysicalValue LowValue LowVar sort)
end Act
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot,AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)
def bootRestriction : SourceOperationInquiry.Context.RawRestrictionAt
 (PhysicalValue:=PairValue (Act.LowValue root visit rec)) (PhysicalVar:=Act.LowVar root visit rec) (sort:=Act.sort root rec)
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap.presentation (C.source root visit rec U7 calculus anchor sourceStage stage)
  (C.sourceCfg root visit rec U7 calculus anchor sourceStage)
  (C.scalar root visit rec U7 calculus anchor sourceStage stage) (C.pair root visit rec U7 calculus anchor sourceStage stage)
  (C.cfg root visit rec U7 calculus anchor sourceStage stage)).erase where
 projection:=(L.installation (C.source root visit rec U7 calculus anchor sourceStage stage)
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.configuration (I.sourceCfg root visit rec U7 calculus anchor sourceStage))).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl
 payload_eq:=rfl

def rawSource (state : (C.runtime root visit rec U7 calculus anchor sourceStage stage).State) :
 SourceOperationInquiry.Context.RawAt (PhysicalValue:=PairValue (Act.LowValue root visit rec))
 (PhysicalVar:=Act.LowVar root visit rec) (sort:=Act.sort root rec)
 (C.runtime root visit rec U7 calculus anchor sourceStage stage) state := by
 rcases state with ⟨⟨⟨count⟩⟩,activation⟩
 cases count with
 | zero => exact bootRestriction root visit rec U7 calculus anchor sourceStage stage
 | succ offset => exact SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Direct.restriction (C.frameAt root visit rec U7 calculus anchor sourceStage stage offset) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.configuration (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.configuration root visit rec U7 calculus anchor sourceStage stage))
private def index (engine : Engine
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap.Run.process
  (C.source root visit rec U7 calculus anchor sourceStage stage) (C.sourceCfg root visit rec U7 calculus anchor sourceStage)
  (C.scalar root visit rec U7 calculus anchor sourceStage stage) (C.pair root visit rec U7 calculus anchor sourceStage stage)
  (C.cfg root visit rec U7 calculus anchor sourceStage stage) (C.strict root visit rec U7 calculus anchor sourceStage stage))) : Nat := by
 rcases engine with ⟨count⟩
 exact count.down

def sourceRawAt : Nat → SourceOperationInquiry.Context.Raw
 (PhysicalValue:=PairValue (Act.LowValue root visit rec)) (PhysicalVar:=Act.LowVar root visit rec) (sort:=Act.sort root rec)
 | 0 => L.liftedRaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (C.source root visit rec U7 calculus anchor sourceStage stage))
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.configuration (I.sourceCfg root visit rec U7 calculus anchor sourceStage))
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence (C.source root visit rec U7 calculus anchor sourceStage stage))
 | count+1 => SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Direct.directRaw
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (C.frameAt root visit rec U7 calculus anchor sourceStage stage count))
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.configuration (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.configuration root visit rec U7 calculus anchor sourceStage stage))
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence (C.frameAt root visit rec U7 calculus anchor sourceStage stage count))

theorem raw_state (state : (C.runtime root visit rec U7 calculus anchor sourceStage stage).State) :
 SourceOperationInquiry.Context.raw (C.runtime root visit rec U7 calculus anchor sourceStage stage)
  (rawSource root visit rec U7 calculus anchor sourceStage stage) state=
 sourceRawAt root visit rec U7 calculus anchor sourceStage stage (index root visit rec U7 calculus anchor sourceStage stage state.engine) := by
 rcases state with ⟨⟨⟨count⟩⟩,activation⟩
 cases count <;> rfl

theorem actual_index (count : Nat) : index root visit rec U7 calculus anchor sourceStage stage
 ((C.runtime root visit rec U7 calculus anchor sourceStage stage).stateAt count).engine=count := by
 have actual := C.actual_node root visit rec U7 calculus anchor sourceStage stage count
 generalize same : ((C.runtime root visit rec U7 calculus anchor sourceStage stage).stateAt count).engine=engine at actual ⊢
 rcases engine with ⟨hidden⟩
 have exactIndex : hidden=ULift.up count := (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap.Run.process
  (C.source root visit rec U7 calculus anchor sourceStage stage) (C.sourceCfg root visit rec U7 calculus anchor sourceStage)
  (C.scalar root visit rec U7 calculus anchor sourceStage stage) (C.pair root visit rec U7 calculus anchor sourceStage stage)
  (C.cfg root visit rec U7 calculus anchor sourceStage stage) (C.strict root visit rec U7 calculus anchor sourceStage stage)).erase_injective rfl rfl
  (congrArg RootInquiryProcessNode.erase actual)
 subst hidden
 rfl

theorem raw_actual (count : Nat) : SourceOperationInquiry.Context.raw
 (C.runtime root visit rec U7 calculus anchor sourceStage stage)
 (rawSource root visit rec U7 calculus anchor sourceStage stage)
 ((C.runtime root visit rec U7 calculus anchor sourceStage stage).stateAt count)=
 sourceRawAt root visit rec U7 calculus anchor sourceStage stage count :=
 (raw_state root visit rec U7 calculus anchor sourceStage stage _).trans
 (congrArg (sourceRawAt root visit rec U7 calculus anchor sourceStage stage) (actual_index root visit rec U7 calculus anchor sourceStage stage count))
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Raw
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
