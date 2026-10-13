import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.ActualQuery.Source

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := PhysicalValue) (Var := PhysicalVar) (sort := slot))
variable (configuration : A.Programme
  (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := slot))

theorem common_classifier
    (projection : (I.stockLaw frame configuration).Projection)
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
    (commonLaw frame configuration).classify projection supplied =
      (I.stockLaw frame configuration).classify projection supplied := rfl

theorem stock_retained : HEq (stockOutcome frame configuration)
    ((I.stockLaw (A.epoch frame) configuration).outcomeAt PUnit.unit (A.Shared.actualOccurrence frame)) :=
  (stockInstalled frame configuration).outcome_heq (A.Shared.actualOccurrence frame) PUnit.unit

theorem common_generated : HEq (commonOutcome frame configuration)
    ((commonLaw (A.epoch frame) configuration).outcomeAt PUnit.unit (A.Shared.actualOccurrence frame)) :=
  (commonInstalled frame configuration).outcome_heq (A.Shared.actualOccurrence frame) PUnit.unit

theorem old_restriction
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
    (commonMaterial frame configuration supplied).1 = I.completeMaterial frame configuration supplied := rfl

theorem query_action_raw : (A.Shared.query frame (programme configuration)).raw =
    actionReader frame (programme configuration) (A.Shared.actualOccurrence frame) := rfl

theorem action_original_raw
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
    actionReader frame (programme configuration) supplied = actionReader frame configuration supplied := rfl

theorem result_action : HEq (A.Shared.resultFace frame (programme configuration)).rootRead
    (actionResultAt frame (programme configuration) (A.Shared.actualOccurrence frame)) := HEq.rfl

theorem result_raw : (A.Shared.resultFace frame (programme configuration)).rootRead.1 =
    (A.Shared.query frame (programme configuration)).raw := rfl

theorem result_value : (A.Shared.resultFace frame (programme configuration)).rootRead.2.2.1 =
    (actionReader frame configuration (A.Shared.actualOccurrence frame)).expression.eval
      (actionReader frame configuration (A.Shared.actualOccurrence frame)).environment :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (A.Shared.baseRoot frame (programme configuration)).toAuthoritativeRoot
    (fun {_current} supplied => actionReader frame (programme configuration) supplied)
    (A.Shared.actualOccurrence frame)

theorem result_trace : (A.Shared.resultFace frame (programme configuration)).rootRead.2.1.2.length =
    remaining (actionReader frame configuration (A.Shared.actualOccurrence frame)).expression :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    (A.Shared.baseRoot frame (programme configuration)).toAuthoritativeRoot
    (fun {_current} supplied => actionReader frame (programme configuration) supplied)
    (A.Shared.actualOccurrence frame)

theorem scalar_inventory : (programme configuration).nextInventory frame = configuration.nextInventory frame := rfl
theorem pair_inventory : (programme configuration).nextPairInventory frame = configuration.nextPairInventory frame := rfl
theorem occurrence_decoder : ((programme configuration).datum frame).nextEnvironmentReadAt =
    ((I.programme configuration).datum frame).nextEnvironmentReadAt := rfl

end SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
