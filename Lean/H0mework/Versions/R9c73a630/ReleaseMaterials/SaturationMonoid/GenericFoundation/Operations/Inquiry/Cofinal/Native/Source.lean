import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Consumer
import H0mework.Realization.Operations.Substitution.Complex
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualNativeBornSourceEffect
open CategoryTheory RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
namespace T
export ActualNativeRelationTransport (paid paid_state paid_raw paid_environment bornStock)
end T
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (nextBorn actualOccurrence)
end S
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (stockCfg)
end AS
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression input expression_eval updated_value residual_value)
end N
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀s,AddCommGroup (Value s)] {sort : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
abbrev born := S.nextBorn frame (AS.stockCfg cfg)

theorem actual_born_registered_expression : (born frame cfg).registered.input.expression =
 N.expression (T.paid frame) := rfl

theorem actual_born_registered_environment : (born frame cfg).registered.input.environment = frame.activeEnvironment := by
 exact RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source.request_environment
  frame.old frame.registered frame.packetAt frame.environment frame.depth

abbrev bornMaterial := T.paid (born frame cfg)
def bornBoundary := relationMap (R := ℤ) (bornMaterial frame cfg).environment
 (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.relations (R := ℤ) (bornMaterial frame cfg))

theorem actual_born_boundary : bornBoundary frame cfg =
 Finsupp.single (born frame cfg).registered.input.expression 1 - Finsupp.single (born frame cfg).event.state.1 1 :=
 (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.relation_boundary (R := ℤ) (bornMaterial frame cfg))

def newEnvCertificate := normalizationCertificate (R := ℤ) (born frame cfg).activeEnvironment (bornBoundary frame cfg)
theorem actual_born_affine_write : relationMap (R := ℤ) (born frame cfg).activeEnvironment
 (newEnvCertificate frame cfg) = bornBoundary frame cfg - constantMap (R := ℤ)
 (valueMap (R := ℤ) (born frame cfg).activeEnvironment (bornBoundary frame cfg)) := source_reduction _ _

theorem actual_born_updated_environment : (N.input (bornMaterial frame cfg)).environment =
 (born frame cfg).activeEnvironment := by
 change (born frame cfg).registered.input.environment +
  ((born frame cfg).activeEnvironment - (born frame cfg).registered.input.environment) = _
 abel

theorem actual_born_effect : (N.expression (bornMaterial frame cfg)).eval
 (born frame cfg).activeEnvironment = effectEvaluator (R := ℤ)
 (bornMaterial frame cfg).environment (bornMaterial frame cfg).increment (bornBoundary frame cfg) := by
 have generated := N.updated_value (R := ℤ) (bornMaterial frame cfg)
 exact (congrArg (fun environment => (N.expression (bornMaterial frame cfg)).eval environment)
  (actual_born_updated_environment frame cfg)).symm.trans generated

theorem actual_born_relation_residual :
 (N.expression (bornMaterial frame cfg)).eval (born frame cfg).activeEnvironment =
 evaluation (R := ℤ) (born frame cfg).activeEnvironment (bornBoundary frame cfg) := by
 have generated := N.residual_value (R := ℤ) (bornMaterial frame cfg)
 change evaluation (R := ℤ) (N.input (bornMaterial frame cfg)).environment (bornBoundary frame cfg) =
  (N.expression (bornMaterial frame cfg)).eval (N.input (bornMaterial frame cfg)).environment at generated
 rw [actual_born_updated_environment] at generated
 exact generated.symm

namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
 (effectFaces paidCoordinate actual_inverse)
end F

theorem actual_born_inverse :
 ((F.effectFaces (bornMaterial frame cfg)).rangeEquiv
  (F.paidCoordinate (bornMaterial frame cfg))).val =
 (N.expression (bornMaterial frame cfg)).eval (born frame cfg).activeEnvironment :=
 (F.actual_inverse (bornMaterial frame cfg)).trans
  (congrArg (fun environment => (N.expression (bornMaterial frame cfg)).eval environment)
   (actual_born_updated_environment frame cfg))

def bornBinding : ∀ target, Var target → Expr Value Var target :=
 fun target name => .const ((born frame cfg).activeEnvironment target name)

theorem actual_binding_environment :
 SourceSubstitution.sourceEnvironment (bornBinding frame cfg) (born frame cfg).registered.input.environment =
 (born frame cfg).activeEnvironment := rfl

def bornEnvArrow : presentationComplex (R := ℤ) (s := sort) (born frame cfg).activeEnvironment ⟶
 presentationComplex (R := ℤ) (s := sort) (born frame cfg).registered.input.environment :=
 SourceSubstitution.complexMorphism (R := ℤ) (bornBinding frame cfg) (born frame cfg).registered.input.environment

end ActualNativeBornSourceEffect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
