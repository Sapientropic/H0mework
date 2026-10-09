import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.InverseSource
import H0mework.Realization.Operations.DerivationReduction
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.OccurrenceConsumer
import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.InventoryTransport
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
namespace J
export RootGeneratedDebtActivationJointSource (initialEvent mathAction)
export RootGeneratedDebtActivationJointSource.Successor (read? Packet join join_whole_paid)
end J

def sourceComponent : SourceNativeProjectionLaw
    (Mother.baseState {frame with depth:=0}).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1} ⊕ (PUnit.{u+1} ⊕ PUnit.{u+1})
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} supplied _ => match projection with
    | .inl _ => type_of% (Joint.material seed frame supplied) × type_of% (occurrenceRaw seed frame supplied) ×
        type_of% (occurrenceExecuted seed frame supplied) ×
        (type_of% (Inverse.paidWritten seed frame supplied) × type_of% (Inverse.result seed frame supplied))
    | .inr (.inl _) => RootGeneratedDebtActivationJointSource.OwnerFree.Raw
        (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort)
    | .inr (.inr _) => SourceOperationDerivations.Derivation
        (occurrenceRaw seed frame supplied).environment (occurrenceRaw seed frame supplied).expression
        (.const ((occurrenceRaw seed frame supplied).expression.eval (occurrenceRaw seed frame supplied).environment))
  project := fun projection {_current} supplied _ => match projection with
    | .inl _ => (Joint.material seed frame supplied,occurrenceRaw seed frame supplied,
        occurrenceExecuted seed frame supplied,(Inverse.paidWritten seed frame supplied,Inverse.result seed frame supplied))
    | .inr (.inl _) => occurrenceRaw seed frame supplied
    | .inr (.inr _) => SourceOperationDerivations.Derivation.normalize
        (occurrenceRaw seed frame supplied).environment (occurrenceRaw seed frame supplied).expression

def installedConfiguration := {configuration seed with
  datum := fun sourceFrame => {
    component := some (sourceComponent seed sourceFrame)
    reader := (configuration seed).datum sourceFrame |>.reader }
  nextPairInventory := fun sourceFrame => some (SourceHistoryCommon.seed (Past.written seed sourceFrame)
    (((sourceComponent seed (epoch sourceFrame)).project (.inl PUnit.unit)
      (Shared.actualOccurrence sourceFrame) PUnit.unit).2.2.2.1)) }

abbrev sourceInstalled := SourceNativeProjectionLaw.InstallationAt.componentCoface
  (Shared.base frame).root.source.base (sourceComponent seed (epoch frame))
def installed := (sourceInstalled seed frame).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.baseRoot frame (installedConfiguration seed)).source.base
    (Shared.queryLaw (epoch frame) (installedConfiguration seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.queryRoot frame (installedConfiguration seed)).source.base
    (Shared.resultLaw (epoch frame) (installedConfiguration seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.resultRoot frame (installedConfiguration seed)).source.base
    (Shared.consumerLaw (epoch frame) (installedConfiguration seed))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.consumerRoot frame (installedConfiguration seed)).source.base
    (Shared.compilationLaw (epoch frame) (installedConfiguration seed)))
def sourceFace : SourceNativeRootSemanticFaceAt (Shared.root frame (installedConfiguration seed))
    (Shared.visit frame (installedConfiguration seed)) where
  projection := (installed seed frame).embed (.inl PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl
theorem original_material : (sourceFace seed frame).rootRead.1 =
    Joint.material seed (epoch frame) (Shared.actualOccurrence frame) := rfl

abbrev installedWritten := SourceHistoryCommon.seed (Past.written seed frame)
  ((sourceFace seed frame).rootRead.2.2.2.1)
theorem installed_born_inventory : (Shared.nextBorn frame (installedConfiguration seed)).pairInventory =
    some (installedWritten seed frame) := rfl
theorem installed_trace (event : PresentedRelationEventAt (Expr (PairValue PhysicalValue) PhysicalVar sort))
    (present : event ∈ (SourceOperationPaidRelations.exposure
      (occurrenceExecuted seed (epoch frame) (Shared.actualOccurrence frame)).2.1.2).trace) :
    event ∈ (installedWritten seed frame).trace := by
  apply (SourceHistoryCommon.parallel_right _ _ _).1
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

theorem inverse_trace_written (event : PresentedRelationEventAt (Expr (PairValue PhysicalValue) PhysicalVar sort))
    (present : event ∈ (SourceOperationPaidRelations.exposure
      (Inverse.result seed (epoch frame) (Shared.actualOccurrence frame)).2.1.2).trace) :
    event ∈ (installedWritten seed frame).trace := by
  apply (SourceHistoryCommon.parallel_right _ _ _).1
  exact Inverse.every_paid_relation seed (epoch frame) (Shared.actualOccurrence frame) event present

abbrev born := Shared.nextBorn frame (installedConfiguration seed)
theorem old_past_born : ∀ event ∈ (Past.written seed frame).trace,
    event ∈ (pairInventory seed (epoch (born seed frame)) (Shared.actualOccurrence (born seed frame))).trace := by
  intro event belongs
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  unfold priorPairInventory
  change event ∈ (SourceHistoryCommon.seed (installedWritten seed frame)
    (liftedInventory seed (epoch (born seed frame)) (Shared.actualOccurrence (born seed frame)))).trace
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event belongs
abbrev completionTransition := InventoryTransport.completionTransition seed frame (born seed frame)
  (old_past_born seed frame)
abbrev output := InventoryTransport.output seed frame (born seed frame) (old_past_born seed frame)

theorem scalar_inventory_next :
    ∀ event ∈ (updatedSeed seed (epoch frame) (Shared.actualOccurrence frame)).trace,
      event ∈ (updatedSeed seed (epoch (Shared.next frame (installedConfiguration seed)))
        (Shared.actualOccurrence (Shared.next frame (installedConfiguration seed)))).trace := by
  unfold Shared.next
  cases frame.action with
  | inr paid => exact InventoryProgramme.inventory_math_next seed frame
  | inl settled =>
      intro event belongs
      apply (SourceHistoryCommon.parallel_left _ _ _).1
      change event ∈ (SourceHistoryCommon.seed seed
        (Pair.relationWrite seed (epoch frame) (Shared.actualOccurrence frame)
          (Pair.disposition seed (epoch frame) (Shared.actualOccurrence frame)))).trace
      exact (SourceHistoryCommon.parallel_right _ _ _).1 event
        (Pair.relation_write_preserves seed (epoch frame) _ _ event belongs)
theorem installed_query : (Shared.query frame (installedConfiguration seed)).raw =
    (Shared.query frame (continuedConfiguration seed)).raw := by
  change Joint.queryRaw seed (epoch frame) (Shared.actualOccurrence frame)
    (Joint.disposition seed (epoch frame) (Shared.actualOccurrence frame)) = _
  rfl

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
