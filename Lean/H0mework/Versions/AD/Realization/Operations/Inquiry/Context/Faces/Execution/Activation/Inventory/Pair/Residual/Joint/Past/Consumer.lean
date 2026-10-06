import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.Source
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Runtime
import H0mework.Versions.AD.Realization.Perfectification.Occurrence.Temporal.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
theorem generate_zero : generate seed frame 0 = exposure seed frame 0 := rfl
theorem generate_next (last : Nat) : generate seed frame (last+1) =
    SourceHistoryCommon.seed (generate seed frame last) (exposure seed frame (last+1)) := rfl
theorem every_stage (last index : Nat) (bounded : index ≤ last) :
    ∀ event ∈ (exposure seed frame index).trace, event ∈ (generate seed frame last).trace := by
  induction last with
  | zero => have same : index=0 := Nat.eq_zero_of_le_zero bounded; subst index; exact fun _ belongs => belongs
  | succ last previous =>
      rw [generate_next]
      by_cases final : index=last+1
      · subst index; exact (SourceHistoryCommon.parallel_right _ _ _).1
      · have earlier : index ≤ last := by omega
        intro event belongs
        exact (SourceHistoryCommon.parallel_left _ _ _).1 event (previous earlier event belongs)

theorem stage_original (index : Nat) :
    (stage frame index).currentState.visit =
      RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathVisit frame.old frame.registered frame.packetAt index := rfl

theorem source_preserved (index : Nat) : (stage frame index).old = frame.old ∧
    (stage frame index).registered = frame.registered ∧ (stage frame index).packetAt = frame.packetAt := ⟨rfl,rfl,rfl⟩

theorem material_current (last : Nat) : (material seed frame last).root = packet seed frame last := by
  cases last <;> rfl

theorem stage_next (index : Nat) : (stage frame index).mathNext = stage frame (index+1) := rfl

theorem actual_stage_trace (index : Nat) : HEq
    (Shared.resultFace (stage frame index) (configuration seed)).rootRead.2.1.2
    (result seed frame index).2.1.2 := actual_trace seed (stage frame index)

theorem source_receipt (index : Nat) : SourceTemporalMaterial.decode
    (Shared.root (stage frame index) (configuration seed)).toAuthoritativeRoot.toLedgerRoot
    (receipt seed frame index) = Shared.visit (stage frame index) (configuration seed) :=
  SourceTemporalMaterial.decode_encode _ _

theorem every_stage_born (index : Nat) (bounded : index ≤ frame.depth) :
    ∀ event ∈ (exposure seed frame index).trace,
      event ∈ (written seed frame).trace := by
  intro event belongs
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event
    (every_stage seed frame frame.depth index bounded event belongs)

theorem current_written_preserved :
    ∀ event ∈ (completeWrittenInventory seed (epoch frame) (Shared.actualOccurrence frame)).trace,
      event ∈ (written seed frame).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1

theorem born_inventory : (Shared.nextBorn frame (continuedConfiguration seed)).pairInventory =
    some (written seed frame) := rfl

theorem continued_stage_trace (index : Nat) : HEq
    (Shared.resultFace (stage frame index) (continuedConfiguration seed)).rootRead.2.1.2
    (result seed frame index).2.1.2 := by
  exact RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace
    (Shared.baseRoot (stage frame index) (continuedConfiguration seed)).toAuthoritativeRoot
      (Shared.visit (stage frame index) (continuedConfiguration seed)).current
    (Mother.baseState {stage frame index with depth:=0}).root.toAuthoritativeRoot
      (Shared.visit (stage frame index) (continuedConfiguration seed)).current
    (queryReader seed (epoch (stage frame index)) (Shared.actualOccurrence (stage frame index)))

theorem continued_scalar_inventory_next :
    ∀ event ∈ (updatedSeed seed (epoch frame) (Shared.actualOccurrence frame)).trace,
      event ∈ (updatedSeed seed (epoch (Shared.next frame (continuedConfiguration seed)))
        (Shared.actualOccurrence (Shared.next frame (continuedConfiguration seed)))).trace := by
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

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
