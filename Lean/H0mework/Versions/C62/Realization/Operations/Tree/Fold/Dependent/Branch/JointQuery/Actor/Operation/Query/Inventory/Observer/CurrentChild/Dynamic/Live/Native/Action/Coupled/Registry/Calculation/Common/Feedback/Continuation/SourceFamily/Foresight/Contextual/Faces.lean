import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Installation
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Engine
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Installed
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t,X t → Expr W X t) (n : Nat) (seed : Lower.SourceFamily.Seed W X s n)
local notation "FrameAt" => M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)

def face (frame : FrameAt) : SourceNativeRootSemanticFaceAt
    (Q.root frame (configuration binding n seed)) (Q.visit frame (configuration binding n seed)) where
  projection := (installation binding n seed frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl
def oldFace (frame : FrameAt) : SourceNativeRootSemanticFaceAt
    (Q.root frame (configuration binding n seed)) (Q.visit frame (configuration binding n seed)) where
  projection := (oldInstallation binding n seed frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl
def stockFace (frame : FrameAt) : SourceNativeRootSemanticFaceAt
    (Lower.SourceFamily.StockObservation.root frame (configuration binding n seed)) (Q.visit frame (configuration binding n seed)) where
  projection := (installation binding n seed frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl
def stockOldFace (frame : FrameAt) : SourceNativeRootSemanticFaceAt
    (Lower.SourceFamily.StockObservation.root frame (configuration binding n seed)) (Q.visit frame (configuration binding n seed)) where
  projection := (oldInstallation binding n seed frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def stockCoreFace (frame : FrameAt) : SourceNativeRootSemanticFaceAt
    (Lower.SourceFamily.StockObservation.root frame (configuration binding n seed)) (Q.visit frame (configuration binding n seed)) where
  projection := (coreInstallation binding n seed frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem core_material (frame : FrameAt) : (stockCoreFace binding n seed frame).rootRead =
    (Reader.Core.material binding n seed (E.epoch frame) (C.actualIndex n frame),
      Reader.Core.pairWritten binding n seed (E.epoch frame) (C.actualIndex n frame)) := rfl

theorem reader_literal (frame : FrameAt) (index : I.OccurrenceIndex n frame) :
    ((configuration binding n seed).datum frame).reader index.2 = R.reader binding n seed frame index.2 := rfl
theorem decoder_preserved (frame : FrameAt) :
    ((configuration binding n seed).datum frame).nextEnvironmentRead =
      ((I.configuration binding n seed).datum frame).nextEnvironmentRead ∧
    ((configuration binding n seed).datum frame).nextEnvironmentReadAt =
      ((I.configuration binding n seed).datum frame).nextEnvironmentReadAt := ⟨rfl,rfl⟩
theorem scalar_inventory_preserved :
    (configuration binding n seed).nextInventory = (I.configuration binding n seed).nextInventory := rfl

theorem actual_material (frame : FrameAt) : (face binding n seed frame).rootRead =
    (R.material binding n seed (E.epoch frame) (C.actualIndex n frame),
      R.pairWritten binding n seed (E.epoch frame) (C.actualIndex n frame)) := rfl
theorem stock_material (frame : FrameAt) : (stockFace binding n seed frame).rootRead =
    (face binding n seed frame).rootRead := rfl
theorem old_low (frame : FrameAt) : (stockOldFace binding n seed frame).rootRead.1 =
    Future.Replay.Source.material (Future.Replay.Binding.at binding n) seed (E.epoch frame)
      (Q.actualOccurrence frame) := rfl
theorem old_high (frame : FrameAt) (depth : frame.depth=0) :
    (stockOldFace binding n seed frame).rootRead.2 (I.native_actual_index n frame depth) =
      I.modelValues binding n seed frame := rfl

theorem actual_raw (frame : FrameAt) : (Q.query frame (configuration binding n seed)).raw =
    (face binding n seed frame).rootRead.1.2.2.2.2.2.2.2.1 := rfl
theorem actual_trace (frame : FrameAt) : HEq
    (Q.resultFace frame (configuration binding n seed)).rootRead.2.1.2
    (R.result binding n seed (E.epoch frame) (C.actualIndex n frame)).2.1.2 :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace
    (Q.baseRoot frame (configuration binding n seed)).toAuthoritativeRoot (Q.visit frame (configuration binding n seed)).current
    (Q.base frame).root.toAuthoritativeRoot (Q.visit frame (configuration binding n seed)).current
    (R.reader binding n seed (E.epoch frame) (Q.actualOccurrence frame))
theorem actual_exposure (frame : FrameAt) :
    SourceOperationPaidRelations.exposure (Q.resultFace frame (configuration binding n seed)).rootRead.2.1.2 =
      SourceOperationPaidRelations.exposure (R.result binding n seed (E.epoch frame) (C.actualIndex n frame)).2.1.2 :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_exposure
    (Q.baseRoot frame (configuration binding n seed)).toAuthoritativeRoot (Q.visit frame (configuration binding n seed)).current
    (Q.base frame).root.toAuthoritativeRoot (Q.visit frame (configuration binding n seed)).current
    (R.reader binding n seed (E.epoch frame) (Q.actualOccurrence frame))

theorem complete_native_preserves (frame : FrameAt) :
    ∀ event ∈ (R.pairWritten binding n seed (E.epoch frame) (C.actualIndex n frame)).trace,
      event ∈ (completePairInventory binding n seed frame).trace := by
  unfold completePairInventory T.preserve
  cases (I.configuration binding n seed).nextPairInventory frame with
  | none => exact fun _ present => present
  | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1
theorem complete_old_preserves (frame : FrameAt) (prior)
    (present : (I.configuration binding n seed).nextPairInventory frame=some prior) :
    ∀ event ∈ prior.trace, event ∈ (completePairInventory binding n seed frame).trace := by
  unfold completePairInventory T.preserve
  rw [present]
  exact (SourceHistoryCommon.parallel_left _ _ _).1
theorem actual_paid_trace_born (frame : FrameAt) :
    ∀ event ∈ (SourceOperationPaidRelations.exposure
      (Q.resultFace frame (configuration binding n seed)).rootRead.2.1.2).trace,
      event ∈ (completePairInventory binding n seed frame).trace := by
  rw [actual_exposure]
  intro event present
  exact complete_native_preserves binding n seed frame event
    (R.complete_native_trace binding n seed (E.epoch frame) (C.actualIndex n frame) event present)
theorem actual_pair_inventory (frame : FrameAt) :
    (Q.nextBorn frame (configuration binding n seed)).pairInventory =
      some (completePairInventory binding n seed frame) := rfl
theorem actual_source_fee (frame : FrameAt) :
    3≤SourceOperationExecution.remaining (Q.query frame (configuration binding n seed)).raw.expression :=
  R.source_fee binding n seed (E.epoch frame) (C.actualIndex n frame)
end Lower.SourceFamily.Foresight.Contextual.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
