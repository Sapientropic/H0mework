import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement CategoryTheory SourceGeneratedScalarDifferentialResidual

namespace Actual
namespace S
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
  (sourceMaterial nativeValue native_value receiver seed successorSeed successorPacket updated_total full_frame complete_word)
namespace L
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.L (Value)
end L
namespace SF
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.SF (Factory Packet)
end SF
end S
variable {W X : PUnit.{u+1} → Type u} [∀ t, AddCommGroup (W t)]
attribute [local instance] SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.levelGroups
variable (factory : S.SF.Factory W X PUnit.unit) (n : Nat)
variable (data : S.SF.Packet (W := W) (X := X) (s := PUnit.unit) n)
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue := S.L.Value W n) (PhysicalVar := X) (sort := PUnit.unit))
variable (language : cfg.LowVar = X)

abbrev material := S.sourceMaterial n data cfg
abbrev faces := effectFaces (material n data cfg)
abbrev whole := wholeFaces (material n data cfg)
def relation := actualRelation (material n data cfg)

theorem actual_native : (faces n data cfg).embedding (paidCoordinate (material n data cfg)) =
    S.nativeValue factory n data cfg language :=
  (actual_inverse (material n data cfg)).trans (S.native_value factory n data cfg language).symm

theorem actual_native_inverse : ((faces n data cfg).rangeEquiv (paidCoordinate (material n data cfg))).val =
    S.nativeValue factory n data cfg language :=
  (actual_inverse (material n data cfg)).trans (S.native_value factory n data cfg language).symm

theorem actual_native_effect : S.nativeValue factory n data cfg language =
    effectEvaluator (R := ℤ) (material n data cfg).environment (material n data cfg).increment (boundary (material n data cfg)) :=
  (S.native_value factory n data cfg language).trans (N.updated_value (R := ℤ) (material n data cfg))

theorem actual_whole_relation : type_of% (relation_recovery (material n data cfg)) := relation_recovery _
theorem actual_generated_differential : type_of% (generated_differential (material n data cfg)) := generated_differential _
theorem actual_complete_frame : type_of% (S.full_frame factory n data cfg language) := S.full_frame _ _ _ _ _

theorem source_trace_in_seed (event) (present : event ∈ (P.exposure (material n data cfg).state.2).trace) :
    event ∈ (S.successorSeed factory n data cfg language).trace := by
  apply (SourceHistoryCommon.parallel_left _ _ _).1 event
  apply (SourceHistoryCommon.parallel_left _ _ _).1 event
  unfold SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.scalar
  unfold SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock.preserve
  split
  · unfold SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Stock.scalar
    unfold SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock.preserve
    split
    · exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
    · exact (SourceHistoryCommon.parallel_right _ _ _).1 event ((SourceHistoryCommon.parallel_left _ _ _).1 event present)
  · apply (SourceHistoryCommon.parallel_right _ _ _).1 event
    unfold SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Stock.scalar
    unfold SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock.preserve
    split
    · exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
    · exact (SourceHistoryCommon.parallel_right _ _ _).1 event ((SourceHistoryCommon.parallel_left _ _ _).1 event present)

abbrev bornHistory := P.prefixHistory
  (RootedAccountedUnfolding.zero (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
    (S.successorPacket factory n data cfg language).1)) (S.successorSeed factory n data cfg language)

theorem actual_boundary_in_born : boundary (material n data cfg) ∈
    (bornHistory factory n data cfg language).relationClosure :=
  P.relations_next (sourceOccurrence (material n data cfg)) (P.exposure (material n data cfg).state.2)
    _ (S.successorSeed factory n data cfg language) (source_trace_in_seed factory n data cfg language)
    (actualRelation (material n data cfg)).property
end Actual
end SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
