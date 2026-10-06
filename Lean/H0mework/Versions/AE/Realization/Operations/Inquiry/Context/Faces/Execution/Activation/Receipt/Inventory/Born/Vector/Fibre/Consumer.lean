import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Vector.Fibre.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector.Fibre
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (bornFrame frame configuration).registered}
variable (supplied : C.Occurrence (bornFrame frame configuration) (current:=current))
theorem full_fibre (left right : Words frame configuration) :
 canonicalResidual (joint frame configuration supplied) left=canonicalResidual (joint frame configuration supplied) right ↔
 ∀ index : Index frame configuration,
  liftMap (R:=ℤ) (left index-right index) ∈ LinearMap.range
   (relationMap (R:=ℤ) (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied))) := by
 calc
  _ ↔ canonicalResidual (joint frame configuration supplied) (left-right)=0 := by rw [map_sub,sub_eq_zero]
  _ ↔ joint frame configuration supplied (left-right)=0 := canonicalResidual_eq_zero_iff _ _
  _ ↔ joint frame configuration supplied left=joint frame configuration supplied right := by rw [map_sub,sub_eq_zero]
  _ ↔ ∀ index : Index frame configuration,
   updateInventory (R:=ℤ) (oldEnvironment frame configuration supplied) (increment frame configuration supplied) (left index)=
   updateInventory (R:=ℤ) (oldEnvironment frame configuration supplied) (increment frame configuration supplied) (right index) := funext_iff
  _ ↔ _ := forall_congr' (fun _ => inventory_fibre_generated (R:=ℤ) _ _ _ _)
theorem inverse_read : (residualEquivRange (joint frame configuration (occurrence frame configuration))
 (inverse frame configuration (occurrence frame configuration))).val=(result frame configuration).2.2.1 := by
 funext index
 exact (result_coordinate frame configuration index).symm
theorem inverse_zero : inverse frame configuration (occurrence frame configuration)=0 ↔ (result frame configuration).2.2.1=0 :=
 (canonicalResidual_eq_zero_iff _ _).trans
  (iff_of_eq (congrArg (fun value : Value frame configuration slot => value=0) (by
   funext index
   exact (result_coordinate frame configuration index).symm)))
theorem next_inverse_canonical : nextInverse frame configuration supplied=
 canonicalResidual (next frame configuration supplied) (actualWords frame configuration) :=
 LinearMap.congr_fun (inducedResidualMap_comp_canonical (update frame configuration supplied)) (actualWords frame configuration)
theorem next_inverse_read :
 (residualEquivRange (next frame configuration (occurrence frame configuration))
  (nextInverse frame configuration (occurrence frame configuration))).val=
 addition frame configuration ((result frame configuration).2.2.1) := by
 have canonical := congrArg (fun value : ResidualCarrier (next frame configuration (occurrence frame configuration)) =>
  (residualEquivRange (next frame configuration (occurrence frame configuration)) value).val)
  (next_inverse_canonical frame configuration (occurrence frame configuration))
 have values : joint frame configuration (occurrence frame configuration) (actualWords frame configuration)=
  (result frame configuration).2.2.1 := by
  funext index
  exact (result_coordinate frame configuration index).symm
 exact canonical.trans ((LinearMap.congr_fun (update frame configuration (occurrence frame configuration)).commutes
  (actualWords frame configuration)).symm.trans (congrArg (addition frame configuration) values))
theorem installed_inverse : (face frame configuration).rootRead.2.2.2.2.1=
 inverse frame configuration (occurrence frame configuration) := rfl
theorem installed_next_inverse : (face frame configuration).rootRead.2.2.2.2.2=
 nextInverse frame configuration (occurrence frame configuration) := rfl
theorem source_ledger : (root frame configuration).toAuthoritativeRoot.toLedgerRoot=
 (sourceRoot frame configuration).toAuthoritativeRoot.toLedgerRoot := rfl
theorem first_whole : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt
 (root frame configuration) (sourceVisit frame configuration)
 (bornFrame frame configuration).currentState.U7 (bornFrame frame configuration).currentState.calculus (reader frame configuration)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt _ _ _ _ _
theorem first_next : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next
 (root frame configuration) (sourceVisit frame configuration)
 (bornFrame frame configuration).currentState.U7 (bornFrame frame configuration).currentState.calculus (reader frame configuration)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next _ _ _ _ _
theorem mother_whole : type_of% (SourceGeneratedInquiryReceiptAction.whole_first (queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.whole_first _ _
theorem mother_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next (queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.literal_next _ _
theorem runtime_next (stage : Nat) : type_of% (SourceGeneratedInquiryReceiptAction.runtime_next (queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme stage) := SourceGeneratedInquiryReceiptAction.runtime_next _ _ stage
abbrev nativeGenerated (stage : Nat) := (Born.nativeGenerated frame configuration stage,
 generated (Faces.Native.nativeFrame frame configuration stage) Faces.Native.R.programme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector.Fibre
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
