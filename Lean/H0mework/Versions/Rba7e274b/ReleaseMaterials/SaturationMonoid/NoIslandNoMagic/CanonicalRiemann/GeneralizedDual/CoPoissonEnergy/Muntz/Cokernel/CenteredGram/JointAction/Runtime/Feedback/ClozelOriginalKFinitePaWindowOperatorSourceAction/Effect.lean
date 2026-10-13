import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Word
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open scoped BigOperators Topology InnerProductSpace

theorem finite_word_source_value (radius : ℝ) (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (completeWindowWord radius).eval environment =
 Native.sourceFields (burnolRadiusZeroExtension radius
  (burnolSourceOnlyCoPoissonWindow radius (OriginalKFullSourceRAction.originalField (environment () ())))) := by
 unfold completeWindowWord
 rw [Expr.eval,cutoff_word_value,Finset.sum_map_toList]
 simp [Expr.eval,cutoffWeight,cutoffPullback,sourcePole,burnolSourceOnlyCoPoissonWindow,
  ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,
  add_apply,sum_apply,map_add,map_sum,map_smul,
  ContinuousLinearMap.toSpanSingleton_apply]

def windowEnvironment (source : Branches) : Env (PairValue (PairValue C.Value)) C.Var := fun _ _ => source

def finiteWindowTrace (radius : ℝ) (source : Branches) :
 Trace (windowEnvironment source) (completeWindowWord radius)
  (.const ((completeWindowWord radius).eval (windowEnvironment source))) := execution _ _

theorem window_from_received_trace (radius : ℝ) (source output : Branches)
 (trace : Trace (windowEnvironment source) (completeWindowWord radius) (.const output)) :
 burnolRadiusRestriction radius (OriginalKFullSourceRAction.originalField output) =
 burnolSourceOnlyCoPoissonWindow radius (OriginalKFullSourceRAction.originalField source) := by
 have generated := trace.sound
 rw [finite_word_source_value] at generated
 change Native.sourceFields (burnolRadiusZeroExtension radius
  (burnolSourceOnlyCoPoissonWindow radius (OriginalKFullSourceRAction.originalField source))) = output at generated
 rw [←generated,Native.source_fields_first,burnolRadiusRestriction_zeroExtension]

/-- First finite inverse stays an actual residual; no injectivity or completed reconstruction is supplied. -/
def firstInverseResidual (radius : ℝ) (source : Branches) : BurnolL2 :=
 OriginalKFullSourceRAction.originalField source - burnolMobiusSourceL2
  (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField
   ((completeWindowWord radius).eval (windowEnvironment source))))

theorem first_inverse_residual_equation (radius : ℝ) (source : Branches) :
 OriginalKFullSourceRAction.originalField source =
 burnolMobiusSourceL2 (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField
  ((completeWindowWord radius).eval (windowEnvironment source)))) + firstInverseResidual radius source := by
 unfold firstInverseResidual
 abel

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
