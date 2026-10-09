import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
theorem actual_query : (Shared.query frame (programme seed)).raw=
 (face seed frame).rootRead.2.1 := rfl
theorem original_material : (face seed frame).rootRead.1=Joint.material seed (epoch frame) (Shared.actualOccurrence frame) := rfl
theorem executed_value : (Shared.resultFace frame (programme seed)).rootRead.2.2.1=
 (occurrenceExecuted seed (epoch frame) (Shared.actualOccurrence frame)).2.2.1 :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
   (Mother.baseState (epoch frame)).root.toAuthoritativeRoot (occurrenceRaw seed (epoch frame))
   (Shared.actualOccurrence frame)).symm
theorem paid_history : (Shared.resultFace frame (programme seed)).rootRead.2.1.2.length=
 remaining (registered seed frame).input.expression :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans
  (congrArg remaining (occurrence_expression seed frame))
theorem completed_value : (Shared.resultFace frame (programme seed)).rootRead.2.2.1=(completed seed frame).1 :=
 (executed_value seed frame).trans (occurrence_value seed frame)
theorem effect_from_source : type_of% (terminal_effect seed frame) := terminal_effect seed frame
theorem born_inventory : (Shared.nextBorn frame (programme seed)).pairInventory=
 some (SourceHistoryCommon.seed (Past.written seed frame) (Inverse.paidWritten seed (epoch frame) (Shared.actualOccurrence frame))) := rfl
variable (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
theorem actual_next (count : Nat) : type_of% (Shared.actual_next initial (programme seed) count) := Shared.actual_next _ _ count
theorem actual_answer (count : Nat) : type_of% (Shared.actual_answer initial (programme seed) count) := Shared.actual_answer _ _ count
theorem actual_input (count : Nat) : type_of% (Shared.actual_query initial (programme seed) count) := Shared.actual_query _ _ count
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
