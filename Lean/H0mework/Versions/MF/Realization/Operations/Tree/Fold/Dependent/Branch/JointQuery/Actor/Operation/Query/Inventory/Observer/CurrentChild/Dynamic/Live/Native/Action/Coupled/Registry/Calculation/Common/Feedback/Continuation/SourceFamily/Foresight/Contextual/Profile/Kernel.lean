import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Written
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Action.Producer
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Kernel
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly
 (nextPacket beforeFrame afterFrame beforeIndex afterIndex beforeState afterState BeforeTarget AfterTarget beforeJointModule afterJointModule
  beforeSource afterSource ReadMorphisms actual_kernel_preserved)
end A
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (face disposition queryWritten pairWritten)
end P
namespace D
export Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch (kernelWord written free_evaluation)
end D
namespace Wr
export Lower.SourceFamily.Foresight.Contextual.Written
 (stock jointStock jointHistory native_written_in_stock stock_in_joint)
end Wr
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (history)
end J
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
local instance beforeNativeModule : Module ℤ (Lower.SourceFamily.Foresight.Model binding (A.beforeState n packet) s 0) :=
 (SourceGeneratedScalarCharacterExact.Carrier ℤ (Lower.SourceFamily.Foresight.completion binding (A.beforeState n packet) s 0)).module
local instance afterNativeModule : Module ℤ (Lower.SourceFamily.Foresight.Model binding (A.afterState binding n packet) s 0) :=
 (SourceGeneratedScalarCharacterExact.Carrier ℤ (Lower.SourceFamily.Foresight.completion binding (A.afterState binding n packet) s 0)).module
local instance beforeJointModule : Module ℤ (A.BeforeTarget binding n packet) := A.beforeJointModule binding n packet
local instance afterJointModule : Module ℤ (A.AfterTarget binding n packet) := A.afterJointModule binding n packet
abbrev beforeFace:=P.face binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet)
abbrev beforeDisposition:=P.disposition binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet)
abbrev afterFace:=P.face binding (n+1) (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) (A.afterIndex binding n packet)
abbrev afterDisposition:=P.disposition binding (n+1) (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) (A.afterIndex binding n packet)
abbrev nextHistory:=Wr.jointHistory binding n packet
variable (sound:GeneratedRelationSoundnessAt (beforeFace binding n packet))
variable (point:GeneratedKernelResidualCoordinateAt (beforeFace binding n packet) sound)
def selectedWord:=D.kernelWord packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet).2 (A.beforeSource binding n packet) sound point

theorem selected_coordinate :
 (J.history packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet).2).completionProjection
  (selectedWord binding n packet sound point)=point.coordinate.val :=
 Classical.choose_spec (Submodule.Quotient.mk_surjective
  (J.history packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet).2).relationInGeneratorClosure point.coordinate.val)

theorem selected_scope_zero : SourceOperationLogic.q (A.beforeSource binding n packet)
 (selectedWord binding n packet sound point).val=0 :=by
 have represented:=selected_coordinate binding n packet sound point
 have generated:=(beforeFace binding n packet).completionEvaluation_mk sound (selectedWord binding n packet sound point)
 exact (D.free_evaluation packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet).2
  (A.beforeSource binding n packet) (selectedWord binding n packet sound point).val).symm.trans
  (generated.symm.trans ((congrArg ((beforeFace binding n packet).completionEvaluation sound) represented).trans point.maps_to_zero))

variable (native:packet.1.depth=0)
include native in
theorem before_actual_index : Lower.SourceFamily.Foresight.Contextual.actualIndex n packet.1=A.beforeIndex n packet :=
 Lower.SourceFamily.Foresight.Installed.native_actual_index n packet.1 native

variable (obstruction:GeneratedCoverageResidualObstructionAt (beforeFace binding n packet) sound)
variable (selected:beforeDisposition binding n packet=.kernelResidual sound obstruction point)
include obstruction selected

theorem selected_written : PresentedRelationEventAt.relation (selectedWord binding n packet sound point).val ∈
 (P.pairWritten binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet)).trace :=by
 apply (SourceHistoryCommon.parallel_right _ _ _).1
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 change PresentedRelationEventAt.relation _ ∈ (D.written packet.2 (A.beforeFrame n packet)
  (A.beforeIndex n packet).2 (A.beforeSource binding n packet) (beforeDisposition binding n packet)).trace
 rw [selected]
 exact (SourceHistoryCommon.parallel_right _ _ _).1 _ List.mem_cons_self

include native in
theorem selected_actual_stock :
 PresentedRelationEventAt.relation (liftMap (selectedWord binding n packet sound point).val) ∈ (Wr.stock binding n packet).trace :=by
 have present:=selected_written binding n packet sound point obstruction selected
 let event : PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s):=
  .relation (selectedWord binding n packet sound point).val
 have inventories:=congrArg
  (fun index=>P.pairWritten binding n packet.2 (A.beforeFrame n packet) index)
  (before_actual_index n packet native)
 have transported : event ∈ (P.pairWritten binding n packet.2 (A.beforeFrame n packet)
  (Lower.SourceFamily.Foresight.Contextual.actualIndex n packet.1)).trace :=
  Eq.mp (congrArg (fun inventory=>event ∈ inventory.trace) inventories.symm) present
 exact Wr.native_written_in_stock binding n packet event transported

include native in
theorem selected_next_relation : liftMap (selectedWord binding n packet sound point).val ∈
 (nextHistory binding n packet).relationClosure :=by
 apply (nextHistory binding n packet).relationStage_le_closure 0
 apply Submodule.subset_span
 change PresentedRelationEventAt.relation _ ∈ (nextHistory binding n packet).observedEvents 0
 simp only [RootGeneratedCofinalHistoryAt.observedEvents,List.range_succ,List.range_zero,
  List.nil_append,List.flatMap_singleton,RootGeneratedCofinalHistoryAt.observation_zero]
 exact Wr.stock_in_joint binding n packet _ (selected_actual_stock binding n packet sound point native obstruction selected)

def forwardVector : (nextHistory binding n packet).generatorClosure :=
 ⟨liftMap (selectedWord binding n packet sound point).val,
  (nextHistory binding n packet).relationClosure_le_generatorClosure
   (selected_next_relation binding n packet sound point native obstruction selected)⟩

include native in
theorem forward_relation : forwardVector binding n packet sound point native obstruction selected ∈
 (nextHistory binding n packet).relationInGeneratorClosure :=
 selected_next_relation binding n packet sound point native obstruction selected

include native in
theorem forward_completion_zero :
 (nextHistory binding n packet).completionProjection (forwardVector binding n packet sound point native obstruction selected)=0 :=
 (Submodule.Quotient.mk_eq_zero _).2 (forward_relation binding n packet sound point native obstruction selected)

omit obstruction selected in
include native in
theorem forward_scope_zero : SourceOperationLogic.q (A.afterSource binding n packet)
 (liftMap (selectedWord binding n packet sound point).val)=0 :=
 Lower.SourceFamily.Foresight.Contextual.Profile.Generated.source_kernel_preserved binding n packet native _
  (selected_scope_zero binding n packet sound point)

omit native in
def NextOutputAt (word:Formal ℤ (PairValue (Lower.Value W (n+1))) X s)
 (forward:(nextHistory binding n packet).generatorClosure)
 (phase:ResidualDispositionOutcome (afterFace binding n packet)) : Type u :=
 match phase with
 | .faithful _ _ _ => (nextHistory binding n packet).CompletionCarrier ≃+
   SourceOperationLogic.Scope (A.afterSource binding n packet)
 | .unsound _ coordinate => ULift.{u,0} (PLift (coordinate.relation ≠ word))
 | .kernelResidual _ _ coordinate => ULift.{u,0} (PLift (coordinate.coordinate.val ≠
   (nextHistory binding n packet).completionProjection forward))
 | .coverageResidual _ _ coordinate => ULift.{u,0} (PLift (coordinate.representative ≠
   SourceOperationLogic.q (A.afterSource binding n packet) word))

omit native obstruction selected in
structure PaidKernel where
 forward:(nextHistory binding n packet).generatorClosure
 forward_word:forward.val=liftMap (selectedWord binding n packet sound point).val
 forward_relation:forward∈(nextHistory binding n packet).relationInGeneratorClosure
 forward_scope:SourceOperationLogic.q (A.afterSource binding n packet)
  (liftMap (selectedWord binding n packet sound point).val)=0
 disposition:NextOutputAt binding n packet (liftMap (selectedWord binding n packet sound point).val)
  forward (afterDisposition binding n packet)

def nextOutput : NextOutputAt binding n packet (liftMap (selectedWord binding n packet sound point).val)
 (forwardVector binding n packet sound point native obstruction selected) (afterDisposition binding n packet) :=by
 generalize nextSelected:afterDisposition binding n packet=phase
 cases phase with
 | faithful nextSound coverage realization =>exact realization.canonicalQuotientAddEquiv
 | unsound _ coordinate =>
  refine ⟨⟨fun same=>coordinate.coordinate_ne_zero ?_⟩⟩
  apply coordinate.coordinate_eq.trans
  apply (congrArg (afterFace binding n packet).freeEvaluation same).trans
  exact (D.free_evaluation (A.nextPacket binding n packet).2 (A.afterFrame binding n packet)
   (A.afterIndex binding n packet).2 (A.afterSource binding n packet) _).trans
    (forward_scope_zero binding n packet sound point native)
 | kernelResidual _ _ coordinate =>
  exact ⟨⟨fun same=>coordinate.coordinate_ne_zero
   (same.trans (forward_completion_zero binding n packet sound point native obstruction selected))⟩⟩
 | coverageResidual nextSound _ coordinate =>
  refine ⟨⟨fun same=>coordinate.representative_not_mem_range ?_⟩⟩
  have zero:coordinate.representative=0:=same.trans (forward_scope_zero binding n packet sound point native)
  exact ⟨0,(map_zero _).trans zero.symm⟩

def paidKernel : PaidKernel binding n packet sound point where
 forward:=forwardVector binding n packet sound point native obstruction selected
 forward_word:=rfl
 forward_relation:=forward_relation binding n packet sound point native obstruction selected
 forward_scope:=forward_scope_zero binding n packet sound point native
 disposition:=nextOutput binding n packet sound point native obstruction selected

omit sound point native obstruction selected in
def OutputAt (phase:ResidualDispositionOutcome (beforeFace binding n packet)) : Type u :=
 match phase with
 | .faithful _ _ _ => (J.history packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet).2).CompletionCarrier ≃+
   SourceOperationLogic.Scope (A.beforeSource binding n packet)
 | .unsound _ coordinate => type_of% coordinate
 | .kernelResidual oldSound _ coordinate => PaidKernel binding n packet oldSound coordinate
 | .coverageResidual _ _ coordinate => type_of% coordinate

omit sound point obstruction selected in
def output : OutputAt binding n packet (beforeDisposition binding n packet) :=by
 generalize selectedEq:beforeDisposition binding n packet=phase
 cases phase with
 | faithful oldSound coverage realization=>exact realization.canonicalQuotientAddEquiv
 | unsound _ coordinate=>exact coordinate
 | kernelResidual oldSound oldObstruction coordinate=>
  exact paidKernel binding n packet oldSound coordinate native oldObstruction selectedEq
 | coverageResidual _ _ coordinate=>exact coordinate

namespace Actual
open RootLawDependentJointStateController
variable {N:WorldRelationNetwork.{u}} {V:Vocabulary.{u}}
variable {H:Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root:SourceNativeLivingRootClosure N V)
variable (visit:SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec:RecognitionAt H root)
local instance physicalGroups:∀t,AddCommGroup (Act.PhysicalValue root visit rec t):=inferInstance
local instance currentGroups (n:Nat) (t:SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Slot root rec):
 AddCommGroup (Lower.Value (Act.LowValue root visit rec) n t):=Lower.groups (Act.LowValue root visit rec) n t
variable (U7:U7ProducerCalculus N) (calculus:U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage count:Nat)
def consume (n:Nat):=Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.output
 (Lower.SourceFamily.Foresight.Contextual.Forecast.Consumed.binding root visit rec) (n+1)
 (Lower.SourceFamily.Foresight.Contextual.Forecast.Consumed.data root visit rec U7 calculus anchor sourceStage stage count n)
 (Lower.SourceFamily.Foresight.Contextual.Forecast.Consumed.actual_depth root visit rec U7 calculus anchor sourceStage stage count n)
end Actual

end Lower.SourceFamily.Foresight.Contextual.Profile.Kernel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
