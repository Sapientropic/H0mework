import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWindowInverseResidualSourceAction.Material
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



open SourceGeneratedScalarDifferentialResidual

theorem literal_source_residual_action (radius : ℝ) (nu : BurnolL2) :
 residualAction radius (Native.sourceFields nu) =
 Native.sourceFields (OriginalKFinitePaWindowOperatorSourceAction.firstInverseResidual radius (Native.sourceFields nu)) := by
 unfold residualAction OriginalKFinitePaWindowOperatorSourceAction.firstInverseResidual
 rw [F.finite_word_source_value]
 simp [finiteWindowAction,OriginalKFinitePaWindowOperatorSourceAction.firstInverseAction,
  Native.source_fields_first,map_sub,ContinuousLinearMap.comp_apply,F.windowEnvironment]

theorem received_source_recovery_action
 (factory : OriginalKFinitePaWindowOperatorSourceAction.SF.Factory (PairValue C.Value) C.Var ())
 (packet : OriginalKFinitePaWindowOperatorSourceAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
 (radius : ℝ) (nu : BurnolL2)
 (write : type_of% (OriginalKFinitePaWindowOperatorSourceAction.finite_stock_generated_source_delta
  factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius (Native.sourceFields nu) (packet.2.2.2.down.symm ▸ ()))) :
 (residualCorrectionCode (Native.sourceFields nu) (receivedResidualAt factory packet radius (Native.sourceFields nu))).eval
 (F.windowEnvironment (Native.sourceFields nu)) = recoveryAction radius (Native.sourceFields nu) := by
 rw [source_correction_action]
 change _ = Native.sourceFields nu - residualAction radius (Native.sourceFields nu)
 rw [literal_source_residual_action]
 congr 1
 unfold receivedResidualAt
 exact congrArg Native.sourceFields (OriginalKFinitePaWindowOperatorSourceAction.received_inverse_residual_source _ _ _ _ _ _ _ _ write)


theorem residual_joint_current (radius : ℝ) (source : F.Branches) : type_of%
 (SourceGeneratedObservationAction.joint_current_source (recoveryAction radius).toLinearMap
  (windowObservation radius).toLinearMap source) :=
 SourceGeneratedObservationAction.joint_current_source _ _ _

theorem residual_joint_next
 (factory : OriginalKFinitePaWindowOperatorSourceAction.SF.Factory (PairValue C.Value) C.Var ())
 (packet : OriginalKFinitePaWindowOperatorSourceAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
 (radius : ℝ) (nu : BurnolL2)
 (write : type_of% (OriginalKFinitePaWindowOperatorSourceAction.finite_stock_generated_source_delta
  factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius (Native.sourceFields nu) (packet.2.2.2.down.symm ▸ ()))) :
 SourceGeneratedObservationAction.jointNext (recoveryAction radius).toLinearMap (windowObservation radius).toLinearMap
  (canonicalResidual (jointResidualObservation radius) (Native.sourceFields nu)) =
 canonicalResidual (windowObservation radius).toLinearMap
  ((residualCorrectionCode (Native.sourceFields nu) (receivedResidualAt factory packet radius (Native.sourceFields nu))).eval
   (F.windowEnvironment (Native.sourceFields nu))) := by
 rw [received_source_recovery_action _ _ _ _ write]
 exact SourceGeneratedObservationAction.joint_next_source _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWindowInverseResidualSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
