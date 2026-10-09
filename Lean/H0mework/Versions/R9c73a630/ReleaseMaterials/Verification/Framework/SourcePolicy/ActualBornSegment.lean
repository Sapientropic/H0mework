import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "SourcePolicyActualBornSegment"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyActualBornSegment
open RootInquiryCompletion SourceOperationEffects
namespace B
export ActualNativeBornSourceEffect
 (actual_born_registered_expression actual_born_registered_environment actual_born_boundary actual_born_affine_write
  actual_born_updated_environment actual_born_effect actual_born_relation_residual actual_born_inverse
  actual_binding_environment bornEnvArrow)
end B
namespace C
export ActualSourceSegmentBornEffect
 (selected selected_settled nativePayload realizedSegment cofinalSegment realizedSegment_source consumeCofinalSegment cofinal_source_span)
end C
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
variable (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
example : type_of% (B.actual_born_registered_expression frame cfg) := B.actual_born_registered_expression frame cfg
example : type_of% (B.actual_born_registered_environment frame cfg) := B.actual_born_registered_environment frame cfg
example : type_of% (B.actual_born_boundary frame cfg) := B.actual_born_boundary frame cfg
example : type_of% (B.actual_born_affine_write frame cfg) := B.actual_born_affine_write frame cfg
example : type_of% (B.actual_born_updated_environment frame cfg) := B.actual_born_updated_environment frame cfg
example : type_of% (B.actual_born_effect frame cfg) := B.actual_born_effect frame cfg
example : type_of% (B.actual_born_relation_residual frame cfg) := B.actual_born_relation_residual frame cfg
example : type_of% (B.actual_born_inverse frame cfg) := B.actual_born_inverse frame cfg
example : type_of% (B.actual_binding_environment frame cfg) := B.actual_binding_environment frame cfg
example : type_of% (B.bornEnvArrow frame cfg) := B.bornEnvArrow frame cfg
variable (native : ActualSourceSegmentBornEffect.AS.AdmissionPacket (W := W) (X := X) (s := s))
example : type_of% (C.selected_settled native) := C.selected_settled native
example : type_of% (C.nativePayload native) := C.nativePayload native
variable (factory : ActualSourceSegmentBornEffect.SF.Factory W X s) (language : cfg.LowVar = X)
example (start : Nat) : type_of% (C.realizedSegment factory frame cfg language start) := C.realizedSegment factory frame cfg language start
example (ordinal : Nat) : type_of% (C.cofinalSegment factory frame cfg language ordinal) := C.cofinalSegment factory frame cfg language ordinal
example (start : Nat) : type_of% (C.realizedSegment_source factory frame cfg language start) := C.realizedSegment_source factory frame cfg language start
example (ordinal : Nat) : type_of% (C.cofinal_source_span factory frame cfg language ordinal) := C.cofinal_source_span factory frame cfg language ordinal
-- This consumer receives the original distance-zero branch or the full dependent native branch.
example {Result : Sort v} (ordinal : Nat)
 (admission : ActualSourceSegmentBornEffect.D.distance factory frame cfg language
  (ActualSourceSegmentBornEffect.D.index factory frame cfg language ordinal+1) = 0 → Result)
 (nativeConsumer : (branch : ActualSourceSegmentBornEffect.NativeSegmentAt factory frame cfg language
  (ActualSourceSegmentBornEffect.D.index factory frame cfg language ordinal+1)) →
  type_of% (C.nativePayload branch.1) → Result) : Result :=
 C.consumeCofinalSegment factory frame cfg language ordinal admission nativeConsumer

#print axioms B.actual_born_registered_expression
#print axioms B.actual_born_registered_environment
#print axioms B.actual_born_boundary
#print axioms B.actual_born_affine_write
#print axioms B.actual_born_updated_environment
#print axioms B.actual_born_effect
#print axioms B.actual_born_relation_residual
#print axioms B.actual_born_inverse
#print axioms B.actual_binding_environment
#print axioms B.bornEnvArrow
#print axioms C.selected_settled
#print axioms C.nativePayload
#print axioms C.realizedSegment
#print axioms C.cofinalSegment
#print axioms C.realizedSegment_source
#print axioms C.consumeCofinalSegment
#print axioms C.cofinal_source_span
end SourcePolicyActualBornSegment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
