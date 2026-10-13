import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Complete
import H0mework.Realization.Operations.Action
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

/-- This is the finite programme's actual source action, not a constructor fed a completed readout. -/
def finiteWindowAction (radius : ℝ) : F.Branches →L[ℂ] F.Branches :=
 Native.sourceFields.comp ((burnolRadiusZeroExtension radius).comp
  ((burnolSourceOnlyCoPoissonWindow radius).comp OriginalKFullSourceRAction.originalField))

def residualAction (radius : ℝ) : F.Branches →L[ℂ] F.Branches :=
 ContinuousLinearMap.id ℂ F.Branches - F.firstInverseAction.comp (finiteWindowAction radius)

def recoveryAction (radius : ℝ) : F.Branches →L[ℂ] F.Branches :=
 ContinuousLinearMap.id ℂ F.Branches - residualAction radius

def residualCorrectionCode (source residual : F.Branches) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (.const source)
  (.linear (s:=()) (t:=()) (-ContinuousLinearMap.id ℂ F.Branches).toLinearMap.toAddMonoidHom (.const residual))

def correctionRaw (source residual : F.Branches) : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue (PairValue C.Value)) (Var:=C.Var) (sort:=()) :=
 ⟨F.windowEnvironment source,residualCorrectionCode source residual⟩

def correctionTrace (source residual : F.Branches) :
 Trace (correctionRaw source residual).environment (correctionRaw source residual).expression
  (.const ((correctionRaw source residual).expression.eval (correctionRaw source residual).environment)) := execution _ _

theorem source_correction_action (source residual : F.Branches) :
 (residualCorrectionCode source residual).eval (F.windowEnvironment source) = source-residual := by
  simp [residualCorrectionCode, Expr.eval, sub_eq_add_neg]

def windowObservation (radius : ℝ) : F.Branches →L[ℂ] BurnolRadiusIntervalL2 radius :=
 (burnolSourceOnlyCoPoissonWindow radius).comp OriginalKFullSourceRAction.originalField

theorem actual_window_correction_effect (radius : ℝ) (source residual : F.Branches) :
 windowObservation radius ((residualCorrectionCode source residual).eval (F.windowEnvironment source)) -
 windowObservation radius source = - windowObservation radius residual := by
 rw [source_correction_action,map_sub]
 abel

def jointResidualObservation (radius : ℝ) :=
 SourceGeneratedObservationAction.jointObservation (recoveryAction radius).toLinearMap (windowObservation radius).toLinearMap

theorem complete_residual_action_fibre (radius : ℝ) (left right : F.Branches) : type_of%
 (SourceGeneratedObservationAction.joint_fibre_iff (recoveryAction radius).toLinearMap (windowObservation radius).toLinearMap left right) :=
 SourceGeneratedObservationAction.joint_fibre_iff _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWindowInverseResidualSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
