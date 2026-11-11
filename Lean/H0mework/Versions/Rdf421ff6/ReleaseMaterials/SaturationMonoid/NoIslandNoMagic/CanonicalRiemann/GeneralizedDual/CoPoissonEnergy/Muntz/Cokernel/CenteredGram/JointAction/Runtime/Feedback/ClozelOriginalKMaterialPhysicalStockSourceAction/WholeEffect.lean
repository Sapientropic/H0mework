import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Whole
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t,AddCommGroup (Value t)] {sort : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=sort))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=sort))

/-- The actual whole callback pays its registered source material residual; the raw trace endpoint and updated environment stay distinct. -/
theorem whole_registered_native_effect (whole : SourceFamilyActualCurrentMaterialRootedEffect.BornWholeWrite frame cfg)
 (value : Value sort) (endpoint : (ActualNativeRelationTransport.paid frame).state.1 = .const value) :
 (SourceFamilyActualCurrentMaterialRootedEffect.B.born frame cfg).registered.input.expression.eval
  (SourceFamilyActualCurrentMaterialRootedEffect.B.born frame cfg).registered.input.environment =
 (ActualNativeRelationTransport.paid frame).raw.effect
  (ActualNativeRelationTransport.paid frame).environment (ActualNativeRelationTransport.paid frame).increment := by
 rw [whole.source_environment,whole.source_expression,
  RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression_eval,endpoint]
 simp only [Expr.eval]
 have paid := (ActualNativeRelationTransport.paid frame).state.2.sound
 rw [endpoint] at paid
 simp only [Expr.eval] at paid
 change (ActualNativeRelationTransport.paid frame).raw.eval
  ((ActualNativeRelationTransport.paid frame).environment + (ActualNativeRelationTransport.paid frame).increment) - value = _
 rw [Expr.eval_update,paid]
 abel

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
