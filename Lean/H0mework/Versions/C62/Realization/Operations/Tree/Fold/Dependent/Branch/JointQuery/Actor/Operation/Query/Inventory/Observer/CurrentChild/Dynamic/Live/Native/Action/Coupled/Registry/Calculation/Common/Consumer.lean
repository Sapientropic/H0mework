import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Raw
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Cofinal.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Syntax.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationScalarInventoryLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot, AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
local instance lowFamily : ∀ slot, AddCommGroup (Act.LowValue root visit rec slot) := inferInstance
local instance : AddCommGroup (Act.LowValue root visit rec (Act.sort root rec)) := lowFamily root visit rec (Act.sort root rec)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)
theorem actual_environment (offset : Nat) : SourceOperationInquiry.Context.readEnv
 (C.runtime root visit rec U7 calculus anchor sourceStage stage)
 (rawSource root visit rec U7 calculus anchor sourceStage stage)
 ((C.runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)=
 (sourceRawAt root visit rec U7 calculus anchor sourceStage stage offset).environment :=
 congrArg (fun raw => raw.environment) (raw_actual root visit rec U7 calculus anchor sourceStage stage offset)

theorem actual_increment (offset : Nat) : SourceOperationInquiry.Context.increment
 (C.runtime root visit rec U7 calculus anchor sourceStage stage)
 (rawSource root visit rec U7 calculus anchor sourceStage stage)
 ((C.runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)=
 (sourceRawAt root visit rec U7 calculus anchor sourceStage stage (offset+1)).environment-
 (sourceRawAt root visit rec U7 calculus anchor sourceStage stage offset).environment := by
 change SourceOperationInquiry.Context.readEnv _ _
  ((C.runtime root visit rec U7 calculus anchor sourceStage stage).stateAt (offset+1))-
  SourceOperationInquiry.Context.readEnv _ _
   ((C.runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)=_
 rw [actual_environment,actual_environment]

theorem actual_stage (offset : Nat) : SourceOperationInquiry.Context.History.stageInventory
 (C.runtime root visit rec U7 calculus anchor sourceStage stage)
 (rawSource root visit rec U7 calculus anchor sourceStage stage) offset=
 SourceOperationScalarRelations.updateInventory (R:=ℤ)
  (sourceRawAt root visit rec U7 calculus anchor sourceStage stage offset).environment
  ((sourceRawAt root visit rec U7 calculus anchor sourceStage stage (offset+1)).environment-
   (sourceRawAt root visit rec U7 calculus anchor sourceStage stage offset).environment) := by
 unfold SourceOperationInquiry.Context.History.stageInventory
 rw [actual_environment,actual_increment]

theorem inverse_whole (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_write
 (C.runtime root visit rec U7 calculus anchor sourceStage stage)
 (rawSource root visit rec U7 calculus anchor sourceStage stage)
 ((C.runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_write _ _ _
theorem inverse_next (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_next
 (C.runtime root visit rec U7 calculus anchor sourceStage stage)
 (rawSource root visit rec U7 calculus anchor sourceStage stage)
 ((C.runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_next _ _ _
theorem inverse_recovered (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_execution
 (C.runtime root visit rec U7 calculus anchor sourceStage stage)
 (rawSource root visit rec U7 calculus anchor sourceStage stage)
 ((C.runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_execution _ _ _

theorem full_future_read (offset bound : Nat)
 (word : SourceOperationInquiry.Context.History.Words
  (PhysicalValue:=SourceOperationScalarInventoryLift.PairValue (Act.LowValue root visit rec)) (PhysicalVar:=Act.LowVar root visit rec) (sort:=Act.sort root rec))
 (index : Fin (bound+1)) : type_of%
 (SourceOperationInquiry.Context.Faces.Cofinal.read_source
  (C.runtime root visit rec U7 calculus anchor sourceStage stage)
  (rawSource root visit rec U7 calculus anchor sourceStage stage) offset bound word index) :=
 SourceOperationInquiry.Context.Faces.Cofinal.read_source _ _ _ _ _ _
theorem full_future_next (offset : Nat)
 (word : SourceOperationInquiry.Context.History.Words
  (PhysicalValue:=SourceOperationScalarInventoryLift.PairValue (Act.LowValue root visit rec)) (PhysicalVar:=Act.LowVar root visit rec) (sort:=Act.sort root rec)) : type_of%
 (SourceOperationInquiry.Context.Faces.Cofinal.next_source
  (C.runtime root visit rec U7 calculus anchor sourceStage stage)
  (rawSource root visit rec U7 calculus anchor sourceStage stage) offset word) :=
 SourceOperationInquiry.Context.Faces.Cofinal.next_source _ _ _ _
theorem full_word_readback (offset : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Cofinal.complete_word_readback
  (C.runtime root visit rec U7 calculus anchor sourceStage stage)
  (rawSource root visit rec U7 calculus anchor sourceStage stage) offset) :=
 SourceOperationInquiry.Context.Faces.Cofinal.complete_word_readback _ _ _
theorem moving_equation (offset : Nat) : type_of%
 (SourceOperationInquiry.Context.Syntax.moving_equation
  (C.runtime root visit rec U7 calculus anchor sourceStage stage)
  (rawSource root visit rec U7 calculus anchor sourceStage stage)
  ((C.runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Syntax.moving_equation _ _ _
theorem complete_future_fibre (offset : Nat)
 (first second : SourceOperationInquiry.Context.History.Words
 (PhysicalValue:=SourceOperationScalarInventoryLift.PairValue (Act.LowValue root visit rec))
 (PhysicalVar:=Act.LowVar root visit rec) (sort:=Act.sort root rec)) : type_of%
 (SourceOperationInquiry.Context.Faces.Cofinal.source_fibre
  (C.runtime root visit rec U7 calculus anchor sourceStage stage)
  (rawSource root visit rec U7 calculus anchor sourceStage stage) offset first second) :=
 SourceOperationInquiry.Context.Faces.Cofinal.source_fibre _ _ _ _ _
theorem full_tail_query (count : Nat) : sourceRawAt root visit rec U7 calculus anchor sourceStage stage (count+1)=
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.query
  (C.frameAt root visit rec U7 calculus anchor sourceStage stage count)
  (C.cfg root visit rec U7 calculus anchor sourceStage stage)).raw := rfl

theorem boot_full_query : (sourceRawAt root visit rec U7 calculus anchor sourceStage stage 0).expression.eval
 (sourceRawAt root visit rec U7 calculus anchor sourceStage stage 0).environment=
 ((SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.query
  (C.source root visit rec U7 calculus anchor sourceStage stage)
  (C.sourceCfg root visit rec U7 calculus anchor sourceStage)).raw.expression.eval
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.query
   (C.source root visit rec U7 calculus anchor sourceStage stage)
   (C.sourceCfg root visit rec U7 calculus anchor sourceStage)).raw.environment,0) :=
 Lower.source_eval (C.source root visit rec U7 calculus anchor sourceStage stage)
 (I.sourceCfg root visit rec U7 calculus anchor sourceStage)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
