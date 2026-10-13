import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWindowInverseResidualSourceAction.Source
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


/-- Literal finite cutoff programme fed the actual correction, before any window read. -/
def residualWindowCode (radius : ℝ) (source residual : F.Branches) :
 Expr (PairValue (PairValue C.Value)) C.Var () :=
 (F.completeWindowWord radius).subst (fun _ _ => residualCorrectionCode source residual)

def residualStockCode (radius : ℝ) (source residual : F.Branches) :
 Expr (PairValue (PairValue C.Value)) C.Var () := .add (.var ()) (residualWindowCode radius source residual)

def residualWindowTrace (radius : ℝ) (source residual : F.Branches) :
 Trace (F.windowEnvironment source) (residualWindowCode radius source residual)
  (.const ((residualWindowCode radius source residual).eval (F.windowEnvironment source))) := execution _ _

theorem residual_window_source_value (radius : ℝ) (source residual : F.Branches)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (residualWindowCode radius source residual).eval environment =
 Native.sourceFields (burnolRadiusZeroExtension radius
  (windowObservation radius (source-residual))) := by
 unfold residualWindowCode
 rw [Expr.eval_subst,F.finite_word_source_value]
 congr 2
 simp [residualCorrectionCode,Expr.eval,sub_eq_add_neg,windowObservation,ContinuousLinearMap.comp_apply]

theorem residual_stock_source_value (radius : ℝ) (source residual : F.Branches)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (residualStockCode radius source residual).eval environment = environment () () +
 Native.sourceFields (burnolRadiusZeroExtension radius (windowObservation radius (source-residual))) := by
 change environment () () + (residualWindowCode radius source residual).eval environment = _
 rw [residual_window_source_value]

theorem residual_window_from_received_trace (radius : ℝ) (source residual output : F.Branches)
 (trace : Trace (F.windowEnvironment source) (residualWindowCode radius source residual) (.const output)) :
 burnolRadiusRestriction radius (OriginalKFullSourceRAction.originalField output) - windowObservation radius source =
 - windowObservation radius residual := by
 have generated := trace.sound
 rw [residual_window_source_value] at generated
 change Native.sourceFields (burnolRadiusZeroExtension radius (windowObservation radius (source-residual))) = output at generated
 rw [←generated,Native.source_fields_first,burnolRadiusRestriction_zeroExtension,map_sub]
 abel

theorem residual_window_actual_effect (radius : ℝ) (source residual : F.Branches) :
 (F.completeWindowWord radius).effect (F.windowEnvironment source) (F.windowEnvironment (-residual)) =
 Native.sourceFields (burnolRadiusZeroExtension radius (-windowObservation radius residual)) := by
 have generated := (F.completeWindowWord radius).eval_update (F.windowEnvironment source) (F.windowEnvironment (-residual))
 rw [F.finite_word_source_value,F.finite_word_source_value] at generated
 change Native.sourceFields (burnolRadiusZeroExtension radius
  (windowObservation radius (source + -residual))) =
  Native.sourceFields (burnolRadiusZeroExtension radius (windowObservation radius source)) + _ at generated
 rw [map_add,map_neg,map_add,map_neg,map_add,map_neg] at generated
 simpa only [map_neg] using add_left_cancel generated.symm

/-- The correction consumes the previous real window write, not an assumed inverse equality. -/
def receivedResidualAt (factory : OriginalKFinitePaWindowOperatorSourceAction.SF.Factory (PairValue C.Value) C.Var ())
 (packet : OriginalKFinitePaWindowOperatorSourceAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
 (radius : ℝ) (source : F.Branches) : F.Branches :=
 Native.sourceFields (OriginalKFinitePaWindowOperatorSourceAction.receivedFirstInverseResidual
  factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source (packet.2.2.2.down.symm ▸ ()))
attribute [irreducible] receivedResidualAt

theorem received_residual_source (factory : OriginalKFinitePaWindowOperatorSourceAction.SF.Factory (PairValue C.Value) C.Var ())
 (packet : OriginalKFinitePaWindowOperatorSourceAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
 (radius : ℝ) (source : F.Branches)
 (write : type_of% (OriginalKFinitePaWindowOperatorSourceAction.finite_stock_generated_source_delta
  factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source (packet.2.2.2.down.symm ▸ ()))) :
 OriginalKFullSourceRAction.originalField (receivedResidualAt factory packet radius source) =
 OriginalKFinitePaWindowOperatorSourceAction.firstInverseResidual radius source := by
 unfold receivedResidualAt
 rw [Native.source_fields_first]
 exact OriginalKFinitePaWindowOperatorSourceAction.received_inverse_residual_source _ _ _ _ _ _ _ _ write

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWindowInverseResidualSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
