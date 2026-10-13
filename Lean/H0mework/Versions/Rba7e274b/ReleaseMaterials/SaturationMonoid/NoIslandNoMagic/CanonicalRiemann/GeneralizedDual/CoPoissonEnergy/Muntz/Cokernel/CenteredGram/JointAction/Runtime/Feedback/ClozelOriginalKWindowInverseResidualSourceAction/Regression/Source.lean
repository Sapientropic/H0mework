import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWindowInverseResidualSourceAction.Physical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWindowInverseResidualSourceAction.Observation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWindowInverseResidualSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace F
export OriginalKFinitePaWindowOperatorSourceAction (Branches firstInverseAction completeWindowWord finite_word_source_value windowEnvironment)
end F
namespace C
export OriginalKFullSourceRAction.C (Value Var)
end C
namespace Native
export OriginalKBoundaryNativeSourceAction (sourceFields source_fields_first)
end Native




open scoped InnerProductSpace

theorem zero_source_correction (radius : ℝ) (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (residualWindowCode radius 0 0).eval environment = 0 := by
 rw [residual_window_source_value]
 simp

theorem explicit_residual_override (radius : ℝ) (source residual : F.Branches)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (residualStockCode radius source residual).eval environment - environment () () =
 Native.sourceFields (burnolRadiusZeroExtension radius (windowObservation radius (source-residual))) := by
 rw [residual_stock_source_value]
 exact add_sub_cancel_left _ _

theorem erasing_residual_price_owes_visible_cost (radius : ℝ) (source residual : F.Branches)
 (noEffect : windowObservation radius (source-residual) = windowObservation radius source) :
 windowObservation radius residual = 0 := by
 rw [map_sub] at noEffect
 exact (sub_eq_self.mp noEffect)

theorem faithful_residual_erasure_requires_recovery (radius : ℝ) (source : F.Branches)
 (erase : OriginalKFinitePaWindowOperatorSourceAction.firstInverseResidual radius source = 0) :
 OriginalKFullSourceRAction.originalField source = burnolMobiusSourceL2
  (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField
   ((F.completeWindowWord radius).eval (F.windowEnvironment source)))) := by
 exact sub_eq_zero.mp erase

theorem correction_does_not_drop_source_stock (radius : ℝ) (source residual : F.Branches)
 (environment : Env (PairValue (PairValue C.Value)) C.Var)
 (drop : (residualStockCode radius source residual).eval environment =
  (residualWindowCode radius source residual).eval environment) : environment () () = 0 := by
 change environment () () + _ = _ at drop
 exact (add_eq_right.mp drop)

theorem same_window_fibre_keeps_next_price (radius : ℝ) (left right : F.Branches)
 (same : windowObservation radius left = windowObservation radius right) : type_of%
 (SourceGeneratedObservationAction.fibre_action_equation (recoveryAction radius).toLinearMap
  (windowObservation radius).toLinearMap left right same) :=
 SourceGeneratedObservationAction.fibre_action_equation _ _ _ _ same

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWindowInverseResidualSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
