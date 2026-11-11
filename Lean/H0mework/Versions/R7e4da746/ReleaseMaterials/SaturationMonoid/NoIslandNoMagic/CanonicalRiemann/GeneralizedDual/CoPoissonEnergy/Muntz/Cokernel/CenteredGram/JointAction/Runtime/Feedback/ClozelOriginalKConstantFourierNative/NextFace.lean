import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Target

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ConstantFourierNextFace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (root visit originalTarget)
end S
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
variable (event : ExactTemporalCausalRootEventAt (S.root frame cfg).toAuthoritativeRoot.toLedgerRoot (S.visit frame cfg))
variable (face : SourceNativeRootSemanticFaceAt (S.root frame cfg) (S.visit frame.mathNext cfg))

noncomputable def fromNext :
    SourceNativeRootSemanticFaceAt (S.originalTarget frame cfg event).targetRoot
      (S.originalTarget frame cfg event).targetVisit where
  projection := (S.originalTarget frame cfg event).oldProjection face.projection
  active := face.active
  classifier_eq := face.classifier_eq

theorem fromNext_read : HEq (fromNext frame cfg event face).rootRead face.rootRead := HEq.rfl

end ConstantFourierNextFace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
