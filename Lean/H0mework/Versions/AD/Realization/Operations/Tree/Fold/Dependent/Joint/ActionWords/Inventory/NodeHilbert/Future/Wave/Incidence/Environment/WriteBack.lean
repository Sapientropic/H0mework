import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Faces
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.WriteBack
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable (frame : Frame.{u})
abbrev nextFrame := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame configuration
def nextTrace := execution (nextFrame frame).rawRead.environment frame.rawRead.expression
def nextWord := SourceOperationScalarPresentation.relationMap (R:=ℤ) (nextFrame frame).rawRead.environment
 (nextTrace frame).relationWords
def reverseRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue Value.{u}) (Var:=Var.{u}) (sort:=Slot.orbit) :=
 ⟨pairEnvironment frame.rawRead.environment ((nextFrame frame).rawRead.environment-frame.rawRead.environment),
  liftExpr (SourceOperationInquiry.Context.Faces.Execution.expression (nextWord frame))⟩
def reverseReader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (_occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) := reverseRaw frame
def reverseResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot
 (reverseReader frame) (Shared.actualOccurrence frame)
def written :=
 let paid := SourceOperationPaidRelations.exposure (reverseResult frame).2.1.2
 match nextPairInventory frame with
 | none => paid
 | some prior => SourceHistoryCommon.seed prior paid

def stage (depth : Nat) : Frame.{u} := {frame with depth:=depth}
abbrev StageMaterial (depth : Nat) := type_of%
 (nextTrace (stage frame depth),nextWord (stage frame depth),reverseRaw (stage frame depth),reverseResult (stage frame depth),written (stage frame depth))
def stageMaterial (depth : Nat) : StageMaterial frame depth :=
 (nextTrace (stage frame depth),nextWord (stage frame depth),reverseRaw (stage frame depth),reverseResult (stage frame depth),written (stage frame depth))
abbrev Packet := Σ depth : Nat,StageMaterial frame depth
def packet (depth : Nat) : Packet frame := ⟨depth,stageMaterial frame depth⟩
def history : Nat → RootedAccountedUnfolding (Packet frame)
 | 0 => .zero (packet frame 0)
 | depth+1 => .occur (packet frame (depth+1)) (.cons (history depth) .nil)
def fromPacket (datum : Packet frame)
 (children : List (RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt
  (Expr (PairValue Value.{u}) Var.{u} Slot.orbit)))) :=
 children.foldr SourceHistoryCommon.seed datum.2.2.2.2.2
def historyWritten (depth : Nat) := (history frame depth).fold (fromPacket frame)
def component : SourceNativeProjectionLaw
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} _ _ => type_of% (sourceRaw frame,sourceResult frame,stageMaterial frame)
 project := fun _ {_current} _ _ => (sourceRaw frame,sourceResult frame,stageMaterial frame)
def installedStage (depth : Nat) := ((component (A.epoch frame)).project PUnit.unit
 (Shared.actualOccurrence frame) PUnit.unit).2.2 depth
def installedPacket (depth : Nat) : Packet (A.epoch frame) := ⟨depth,installedStage frame depth⟩
def installedHistory : Nat → RootedAccountedUnfolding (Packet (A.epoch frame))
 | 0 => .zero (installedPacket frame 0)
 | depth+1 => .occur (installedPacket frame (depth+1)) (.cons (installedHistory depth) .nil)
def installedWritten := (installedHistory frame frame.depth).fold (fromPacket (A.epoch frame))
def programme := {configuration.{u} with
 datum := fun sourceFrame => {
  component := some (component sourceFrame)
  reader := (configuration.datum sourceFrame).reader
  nextEnvironmentRead := (configuration.datum sourceFrame).nextEnvironmentRead }
 nextPairInventory := fun sourceFrame => some (installedWritten sourceFrame) }

def installed := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.source.base (component (A.epoch frame))).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.baseRoot frame programme).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryLaw (A.epoch frame) programme)) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryRoot frame programme).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultLaw (A.epoch frame) programme)) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultRoot frame programme).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerLaw (A.epoch frame) programme)) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerRoot frame programme).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.compilationLaw (A.epoch frame) programme))
def sourceFace : SourceNativeRootSemanticFaceAt
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.root frame programme)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit frame programme) where
 projection := (installed frame).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
abbrev sourceStage (depth : Nat) := (sourceFace frame).rootRead.2.2 depth
abbrev sourceWritten := installedWritten frame
theorem source_stage (depth : Nat) : sourceStage frame depth=stageMaterial (A.epoch frame) depth := rfl
theorem born_inventory : (Shared.nextBorn frame programme).pairInventory=some (sourceWritten frame) := rfl
theorem history_written_zero : historyWritten frame 0=written (stage frame 0) := rfl
theorem history_written_succ (depth : Nat) : historyWritten frame (depth+1)=
 SourceHistoryCommon.seed (historyWritten frame depth) (written (stage frame (depth+1))) := rfl
theorem every_stage (last depth : Nat) (bounded : depth≤last) :
 ∀ event ∈ (written (stage frame depth)).trace,event ∈ (historyWritten frame last).trace := by
 induction last with
 | zero =>
  have same : depth=0 := Nat.eq_zero_of_le_zero bounded
  subst depth
  exact fun _ present => present
 | succ last previous =>
  rw [history_written_succ]
  by_cases final : depth=last+1
  · subst depth
    exact (SourceHistoryCommon.parallel_right _ _ _).1
  · have earlier : depth≤last := by omega
    exact fun event present => (SourceHistoryCommon.parallel_left _ _ _).1 event (previous earlier event present)
theorem installed_history (depth : Nat) : installedHistory frame depth=history (A.epoch frame) depth := by
 induction depth with
 | zero => rfl
 | succ depth prior =>
  change RootedAccountedUnfolding.occur (packet (A.epoch frame) (depth+1))
   (.cons (installedHistory frame depth) .nil)=_
  rw [prior]
  rfl
theorem written_source : sourceWritten frame=historyWritten (A.epoch frame) frame.depth :=
 congrArg (fun tree => tree.fold (fromPacket (A.epoch frame))) (installed_history frame frame.depth)
theorem every_reverse_trace (depth : Nat) (bounded : depth≤frame.depth)
 (event : CofinalHistorySettlement.PresentedRelationEventAt (Expr (PairValue Value.{u}) Var.{u} Slot.orbit))
 (present : event ∈ (SourceOperationPaidRelations.exposure (reverseResult (stage frame depth)).2.1.2).trace) :
 event ∈ (sourceWritten frame).trace := by
 rw [written_source]
 apply every_stage (A.epoch frame) frame.depth depth bounded event
 change event ∈ (written (stage frame depth)).trace
 unfold written
 cases nextPairInventory (stage frame depth) with
 | none => exact present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem old_pair_written (prior : RootedAccountedUnfolding
 (CofinalHistorySettlement.PresentedRelationEventAt (Expr (PairValue Value.{u}) Var.{u} Slot.orbit)))
 (actual : frame.pairInventory=some prior) (event)
 (present : event ∈ prior.trace) : event ∈ (written frame).trace := by
 unfold written nextPairInventory
 rw [actual]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event
  ((SourceHistoryCommon.parallel_left _ _ _).1 event present)
theorem old_pair_born (prior : RootedAccountedUnfolding
 (CofinalHistorySettlement.PresentedRelationEventAt (Expr (PairValue Value.{u}) Var.{u} Slot.orbit)))
 (actual : frame.pairInventory=some prior) (event)
 (present : event ∈ prior.trace) : event ∈ (sourceWritten frame).trace := by
 rw [written_source]
 apply every_stage (A.epoch frame) frame.depth frame.depth (Nat.le_refl _) event
 exact old_pair_written (stage (A.epoch frame) frame.depth) prior actual event present
theorem inventory_next (prior : RootedAccountedUnfolding
 (CofinalHistorySettlement.PresentedRelationEventAt (Expr (PairValue Value.{u}) Var.{u} Slot.orbit)))
 (actual : frame.pairInventory=some prior) :
 ∀ event ∈ prior.trace,event ∈ ((SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame programme).pairInventory.getD prior).trace := by
 unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
 cases frame.action with
 | inr paid =>
  rw [show frame.mathNext.pairInventory=some prior from actual]
  exact fun _ present => present
 | inl settled =>
  rw [born_inventory]
  exact old_pair_born frame prior actual
theorem source_value : (Shared.resultFace frame programme).rootRead.2.2.1=
 (sourceRaw (A.epoch frame)).expression.eval (sourceRaw (A.epoch frame)).environment :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (Shared.baseRoot frame programme).toAuthoritativeRoot (Shared.datum frame programme).reader
  (Shared.actualOccurrence frame)
theorem same_source_value : (Shared.resultFace frame programme).rootRead.2.2.1=
 (Shared.resultFace frame configuration).rootRead.2.2.1 :=
 (source_value frame).trans (PaidSourceContentEnvironment.source_value frame).symm
theorem actual_next_environment :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame programme).rawRead.environment=
 (nextFrame frame).rawRead.environment := by
 rw [RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.raw_environment,
  RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.raw_environment]
 unfold nextFrame SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
 cases frame.action with
 | inr paid => rfl
 | inl settled => rfl

abbrev runtime (initialFrame : Frame.{u}) := Shared.runtime initialFrame programme
abbrev actualRawSource (initialFrame : Frame.{u}) := Configured.rawSource initialFrame programme
abbrev actualState (initialFrame : Frame.{u}) (stage : Nat) := (runtime initialFrame).stateAt stage
theorem actual_next_raw (initialFrame : Frame.{u}) (stage : Nat) :
 SourceOperationInquiry.Context.readEnv (runtime initialFrame) (actualRawSource initialFrame)
  (actualState initialFrame stage).tick.nextState=
 (nextFrame (Shared.frames initialFrame programme stage)).rawRead.environment :=
 (Configured.environment_actual initialFrame programme (stage+1)).trans
  (actual_next_environment (Shared.frames initialFrame programme stage))
theorem same_reverse_word (initialFrame : Frame.{u}) (stage : Nat) :
 SourceOperationInquiry.Context.Faces.Reverse.nextWord (runtime initialFrame) (actualRawSource initialFrame)
  (actualState initialFrame stage)=nextWord (Shared.frames initialFrame programme stage) := by
 unfold SourceOperationInquiry.Context.Faces.Reverse.nextWord
 change SourceOperationScalarPresentation.relationMap (R:=ℤ)
  (SourceOperationInquiry.Context.readEnv (runtime initialFrame) (actualRawSource initialFrame) (actualState initialFrame stage).tick.nextState)
  (SourceOperationExecution.execution
   (SourceOperationInquiry.Context.readEnv (runtime initialFrame) (actualRawSource initialFrame) (actualState initialFrame stage).tick.nextState)
   (SourceOperationInquiry.Context.raw (runtime initialFrame) (actualRawSource initialFrame) (actualState initialFrame stage)).expression).relationWords=_
 rw [actual_next_raw,Configured.raw_actual]
 rfl
private theorem expression_pair
 (word : SourceOperationScalarRelations.Formal ℤ Value.{u} Var.{u} Slot.orbit)
 (old delta : Env Value.{u} Var.{u}) :
 (liftExpr (SourceOperationInquiry.Context.Faces.Execution.expression word)).eval (pairEnvironment old delta)=
 SourceOperationScalarRelations.updateInventory (R:=ℤ) old delta word := by
 rw [eval_liftExpr,SourceOperationInquiry.Context.Faces.Execution.expression_eval]
 apply Prod.ext
 · rfl
 · apply add_left_cancel (a:=SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=Slot.orbit) old word)
   change SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=Slot.orbit) old word+
    (SourceOperationInquiry.Context.Faces.Execution.expression word).effect old delta=
    SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=Slot.orbit) old word+
    SourceOperationScalarRelations.effectEvaluator (R:=ℤ) (s:=Slot.orbit) old delta word
   rw [← SourceOperationInquiry.Context.Faces.Execution.expression_eval word old,← Expr.eval_update,
    SourceOperationInquiry.Context.Faces.Execution.expression_eval]
   simpa only [SourceOperationInquiry.Context.Faces.Execution.expression_eval,LinearMap.add_apply] using
    LinearMap.congr_fun (SourceOperationScalarRelations.evaluation_update (R:=ℤ) (s:=Slot.orbit) old delta) word
theorem reverse_paid_pair : (reverseResult frame).2.2.1=
 SourceOperationScalarRelations.updateInventory (R:=ℤ) frame.rawRead.environment
  ((nextFrame frame).rawRead.environment-frame.rawRead.environment) (nextWord frame) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot
  (reverseReader frame) (Shared.actualOccurrence frame)).trans
  (expression_pair (nextWord frame) frame.rawRead.environment
   ((nextFrame frame).rawRead.environment-frame.rawRead.environment))
theorem reverse_recovered_pair (initialFrame : Frame.{u}) (stage : Nat) :
 SourceOperationInquiry.Context.Faces.recover (runtime initialFrame) (actualRawSource initialFrame)
  (actualState initialFrame stage)
  (SourceOperationInquiry.Context.Faces.Reverse.reverse (runtime initialFrame) (actualRawSource initialFrame) (actualState initialFrame stage))=
 SourceOperationScalarRelations.updateInventory (R:=ℤ)
  (Shared.frames initialFrame programme stage).rawRead.environment
  ((nextFrame (Shared.frames initialFrame programme stage)).rawRead.environment-
   (Shared.frames initialFrame programme stage).rawRead.environment) (nextWord (Shared.frames initialFrame programme stage)) := by
 have recovered := SourceOperationInquiry.Context.Faces.Reverse.reverse_recover (runtime initialFrame) (actualRawSource initialFrame)
  (actualState initialFrame stage)
 apply recovered.trans
 apply (congrArg (SourceOperationInquiry.Context.Faces.pairInventory (runtime initialFrame) (actualRawSource initialFrame)
  (actualState initialFrame stage)) (same_reverse_word initialFrame stage)).trans
 exact LinearMap.congr_fun
  ((Configured.update_inventory initialFrame programme stage).trans
   (congrArg (fun environment => SourceOperationScalarRelations.updateInventory (R:=ℤ)
    (Shared.frames initialFrame programme stage).rawRead.environment
    (environment-(Shared.frames initialFrame programme stage).rawRead.environment))
    (actual_next_environment (Shared.frames initialFrame programme stage)))) _
theorem reverse_value (initialFrame : Frame.{u}) (stage : Nat) :
 (reverseResult (Shared.frames initialFrame programme stage)).2.2.1=
 SourceOperationInquiry.Context.Faces.recover (runtime initialFrame) (actualRawSource initialFrame)
  (actualState initialFrame stage)
  (SourceOperationInquiry.Context.Faces.Reverse.reverse (runtime initialFrame) (actualRawSource initialFrame) (actualState initialFrame stage)) :=
 (reverse_paid_pair (Shared.frames initialFrame programme stage)).trans (reverse_recovered_pair initialFrame stage).symm

abbrev generated (initialFrame : Frame.{u}) := (runtime initialFrame,actualRawSource initialFrame,
 Configured.withActualFaces initialFrame programme,
 fun stage => (sourceFace (Shared.frames initialFrame programme stage),
  nextTrace (Shared.frames initialFrame programme stage),
  reverseResult (Shared.frames initialFrame programme stage)))
theorem born_content {current : (Shared.nextBorn frame programme).V.Current}
 (occurrence : (Shared.nextBorn frame programme).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
 (Shared.nextBorn frame programme).environment occurrence=
 PaidSourceMacroHistory.environmentAt.{u} (PaidSourceMacroHistory.programme.{u}.eval (A.epoch frame).activeEnvironment) := by
 change PaidSourceMacroHistory.environmentAt.{u} ((Shared.resultFace frame programme).rootRead.2.2.1.1+
  (Shared.resultFace frame programme).rootRead.2.2.1.2)=_
 rw [same_source_value]
 exact congrArg PaidSourceMacroHistory.environmentAt.{u} (paid_environment frame)
theorem macro_current (initialFrame : Frame.{u}) (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current programme initialFrame stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current programme initialFrame stage
theorem no_refill : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill programme frame) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill programme frame
theorem noetherian : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded programme frame) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded programme frame

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.WriteBack
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
