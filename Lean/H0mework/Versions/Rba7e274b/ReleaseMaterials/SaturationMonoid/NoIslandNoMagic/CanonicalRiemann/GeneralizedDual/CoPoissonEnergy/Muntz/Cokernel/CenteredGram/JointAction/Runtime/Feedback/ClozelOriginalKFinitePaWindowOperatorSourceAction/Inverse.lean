import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState

def firstInverseAction : Branches →L[ℂ] Branches :=
 Native.sourceFields.comp (burnolMobiusSourceL2.comp
  (burnolEvenAmbientProjection.comp OriginalKFullSourceRAction.originalField))

def inverseResidualWord (radius : ℝ) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (.var ()) (.linear (s:=()) (t:=()) (-firstInverseAction).toLinearMap.toAddMonoidHom (completeWindowWord radius))

def inverseResidualTrace (radius : ℝ) (source : Branches) :
 Trace (windowEnvironment source) (inverseResidualWord radius)
  (.const ((inverseResidualWord radius).eval (windowEnvironment source))) := execution _ _

theorem inverse_residual_generated (radius : ℝ) (source : Branches) :
 OriginalKFullSourceRAction.originalField ((inverseResidualWord radius).eval (windowEnvironment source)) =
 firstInverseResidual radius source := by
 change OriginalKFullSourceRAction.originalField (source + (-firstInverseAction) ((completeWindowWord radius).eval (windowEnvironment source))) = _
 simp [firstInverseAction,firstInverseResidual,map_add,map_neg,Native.source_fields_first,sub_eq_add_neg]

def completeWindowInventory (radius : ℝ) (source : Branches) :=
 SourceHistoryCommon.seed (SourceOperationPaidRelations.exposure (finiteWindowTrace radius source))
  (SourceOperationPaidRelations.exposure (inverseResidualTrace radius source))

theorem all_forward_steps_charged (radius : ℝ) (source : Branches) :
 (SourceOperationPaidRelations.words (finiteWindowTrace radius source)).length =
  (finiteWindowTrace radius source).length := SourceOperationPaidRelations.complete_steps _

theorem all_inverse_steps_charged (radius : ℝ) (source : Branches) :
 (SourceOperationPaidRelations.words (inverseResidualTrace radius source)).length =
  (inverseResidualTrace radius source).length := SourceOperationPaidRelations.complete_steps _

theorem literal_cutoff_append (radius : ℝ) (m : ℕ+) (rest : List ℕ+)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (cutoffWord radius (m::rest)).eval environment - (cutoffWord radius rest).eval environment =
 cutoffWeight m (cutoffPullback radius m (environment () ())) := by
 change cutoffWeight m (cutoffPullback radius m (environment () ())) + _ - _ = _
 exact add_sub_cancel_right _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
