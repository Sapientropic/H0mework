import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Stage
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualNativeRelationTransport
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (stockCfg generatedStock firstReceiver firstProgramme firstBase firstSelected firstReceipt firstReceiptRaw firstBorn first_native_full first_born_full)
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory)
end SF
end AS
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch Programme)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base baseRoot queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw root visit actualOccurrence frames next nextBorn targetAt)
end S
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (stockEmbedding component stockLaw completeMaterial)
end I
namespace IP
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
 (updatedSeed writtenSeed relationWrite disposition physical)
end IP
namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
 (boundary sourceOccurrence history actualRelation complex source_boundary wholeFaces effectFaces
  generated_relation generated_cochain generated_differential completion_zero relation_recovery whole_paid_trace)
end F
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression input expression_eval)
end N
namespace P
export SourceOperationPaidRelations (exposure prefixHistory relations_next)
end P
namespace T
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end T
section Current
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ s, AddCommGroup (Value s)] {sort : Sorts}
variable (frame : A.M.Frame (Value := Value) (Var := Var) (sort := sort))
variable (base : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

def paid := SourceOperationInquiry.Context.Installation.residualAt (A.epoch frame) (S.actualOccurrence frame)
theorem paid_state : (paid frame).state = frame.event.state := rfl
theorem paid_environment : (paid frame).environment = frame.registered.input.environment := rfl
theorem paid_raw : (paid frame).raw = frame.registered.input.expression := rfl

def bornStock := T.preserve frame.inventory (T.preserve (base.nextInventory frame) (AS.generatedStock frame))
theorem born_stock : (S.nextBorn frame (AS.stockCfg base)).inventory = some (bornStock frame base) := rfl

private theorem preserve_generated {α : Type u} (prior : Option (RootedAccountedUnfolding α))
    (generated : RootedAccountedUnfolding α) (event : α) (present : event ∈ generated.trace) :
    event ∈ (T.preserve prior generated).trace := by
 cases prior with
 | none => exact present
 | some carried => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

theorem paid_in_generated (event) (present : event ∈ (P.exposure (paid frame).state.2).trace) :
    event ∈ (AS.generatedStock frame).trace := by
 let seed := RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator frame.registered.input.expression)
 have within : event ∈ (IP.updatedSeed seed (A.epoch frame) (S.actualOccurrence frame)).trace :=
   (SourceHistoryCommon.parallel_right _ _ _).1 event present
 unfold AS.generatedStock
 change event ∈ (IP.relationWrite seed (A.epoch frame) (S.actualOccurrence frame)
   (IP.disposition seed (A.epoch frame) (S.actualOccurrence frame))).trace
 unfold IP.relationWrite
 cases IP.disposition seed (A.epoch frame) (S.actualOccurrence frame) with
 | faithful _ _ _ => exact within
 | unsound _ _ => exact within
 | kernelResidual _ _ _ => exact (SourceHistoryCommon.parallel_left _ _ _).1 event within
 | coverageResidual _ _ _ => exact within

theorem paid_in_born (event) (present : event ∈ (P.exposure (paid frame).state.2).trace) :
    event ∈ (bornStock frame base).trace :=
 preserve_generated _ _ event (preserve_generated _ _ event (paid_in_generated frame event present))

abbrev bornHistory := P.prefixHistory
 (RootedAccountedUnfolding.zero (S.actualOccurrence (S.nextBorn frame (AS.stockCfg base)))) (bornStock frame base)
theorem new_relation_in_born : F.boundary (paid frame) ∈ (bornHistory frame base).relationClosure :=
 P.relations_next (F.sourceOccurrence (paid frame)) (P.exposure (paid frame).state.2)
  _ (bornStock frame base) (paid_in_born frame base) (F.actualRelation (paid frame)).property

def stockInstalled := (I.stockEmbedding (A.epoch frame) base).trans
 (SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base frame).root.source.base
   (I.component (A.epoch frame) base)) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   (S.baseRoot frame (AS.stockCfg base)).source.base (S.queryLaw (A.epoch frame) (AS.stockCfg base))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   (S.queryRoot frame (AS.stockCfg base)).source.base (S.resultLaw (A.epoch frame) (AS.stockCfg base))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   (S.resultRoot frame (AS.stockCfg base)).source.base (S.consumerLaw (A.epoch frame) (AS.stockCfg base))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   (S.consumerRoot frame (AS.stockCfg base)).source.base (S.compilationLaw (A.epoch frame) (AS.stockCfg base)))
def stockOutcome := (S.root frame (AS.stockCfg base)).source.base.projectionLaw.outcomeAt
 ((stockInstalled frame base).embed PUnit.unit) (S.actualOccurrence frame)
theorem stock_payload : HEq (stockOutcome frame base)
 ((I.stockLaw (A.epoch frame) base).outcomeAt PUnit.unit (S.actualOccurrence frame)) :=
 (stockInstalled frame base).outcome_heq _ _
def typedStockOutcome : type_of% ((I.stockLaw (A.epoch frame) base).outcomeAt PUnit.unit (S.actualOccurrence frame)) :=
 cast (type_eq_of_heq (stock_payload frame base)) (stockOutcome frame base)
theorem typed_stock : typedStockOutcome frame base =
 (I.stockLaw (A.epoch frame) base).outcomeAt PUnit.unit (S.actualOccurrence frame) :=
 eq_of_heq ((cast_heq_iff_heq _ _ _).mpr (stock_payload frame base))
def stockMaterial : type_of% (I.completeMaterial (A.epoch frame) base (S.actualOccurrence frame)) :=
 match typedStockOutcome frame base with
 | .inl active => active.2
 | .inr absent => PEmpty.elim absent
theorem stock_material_source : stockMaterial frame base =
 I.completeMaterial (A.epoch frame) base (S.actualOccurrence frame) := by
 unfold stockMaterial
 rw [typed_stock]
 rfl
theorem stock_paid_state : HEq (stockMaterial frame base).1.1.1.1.1.1.paid.state (paid frame).state := by
 rw [stock_material_source]
 rfl
theorem stock_paid_trace : HEq (stockMaterial frame base).1.1.1.1.1.1.paid.state.2 (paid frame).state.2 := by
 rw [stock_material_source]
 rfl

theorem born_payload (event : ExactTemporalCausalRootEventAt
    (S.root frame (AS.stockCfg base)).toAuthoritativeRoot.toLedgerRoot (S.visit frame (AS.stockCfg base))) : HEq
 ((S.targetAt frame (AS.stockCfg base) event).targetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
  ((S.targetAt frame (AS.stockCfg base) event).oldProjection ((stockInstalled frame base).embed PUnit.unit))
  ((S.targetAt frame (AS.stockCfg base) event).targetRoot.emitted
    (S.targetAt frame (AS.stockCfg base) event).targetInitialVisit.current))
 (stockOutcome frame base) := (S.targetAt frame (AS.stockCfg base) event).oldOutcome_heq _

theorem new_relation_face : type_of% (F.generated_relation (paid frame)) := F.generated_relation _
theorem new_cochain_face : type_of% (F.generated_cochain (paid frame)) := F.generated_cochain _
theorem new_differential : type_of% (F.generated_differential (paid frame)) := F.generated_differential _
theorem new_completion_zero : type_of% (F.completion_zero (paid frame)) := F.completion_zero _
theorem new_whole_recovery : type_of% (F.relation_recovery (paid frame)) := F.relation_recovery _
theorem new_full_trace : type_of% (F.whole_paid_trace (paid frame)) := F.whole_paid_trace _
end Current

end ActualNativeRelationTransport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
