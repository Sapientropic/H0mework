import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Consumer
import H0mework.Arithmetic.TruncatedFourier.BlockStates
import H0mework.Realization.Operations.Execution.Cochain.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open scoped BigOperators Topology InnerProductSpace
namespace C
export OriginalKFullSourceRAction.C (Value Var)
end C
namespace Native
export OriginalKBoundaryNativeSourceAction (sourceFields source_fields_first)
end Native
abbrev Branches := OriginalKDefectAction.Branches

/-- Actual scale/radius source operator, returned to the original carrier. -/
def cutoffPullback (radius : ℝ) (m : ℕ+) : Branches →L[ℂ] Branches :=
 Native.sourceFields.comp
  ((burnolRadiusZeroExtension radius).comp ((burnolWindowScalePullback radius m).comp OriginalKFullSourceRAction.originalField))

def cutoffWeight (m : ℕ+) : Branches →L[ℂ] Branches :=
 (((m:ℕ):ℂ)⁻¹) • ContinuousLinearMap.id ℂ Branches

def sourcePole (radius : ℝ) : Branches →L[ℂ] Branches :=
 Native.sourceFields.comp ((burnolRadiusZeroExtension radius).comp
  ((ContinuousLinearMap.toSpanSingleton ℂ (intervalConstant radius)).comp
   (((-1/2:ℂ) • burnolSourceWindowIntegral).comp
    (burnolTateReciprocalL2.comp OriginalKFullSourceRAction.originalField))))

def cutoffTerm (radius : ℝ) (m : ℕ+) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .linear (s:=()) (t:=()) (cutoffWeight m).toLinearMap.toAddMonoidHom
  (.linear (s:=()) (t:=()) (cutoffPullback radius m).toLinearMap.toAddMonoidHom (.var ()))

def cutoffWord (radius : ℝ) : List ℕ+ → Expr (PairValue (PairValue C.Value)) C.Var ()
 | [] => .const 0
 | m::tail => .add (cutoffTerm radius m) (cutoffWord radius tail)

def completeWindowWord (radius : ℝ) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (cutoffWord radius (burnolCenteredMobiusCutoffFinset radius).toList)
  (.linear (s:=()) (t:=()) (sourcePole radius).toLinearMap.toAddMonoidHom (.var ()))

theorem cutoff_word_value (radius : ℝ) (members : List ℕ+)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (cutoffWord radius members).eval environment =
 (members.map (fun m => cutoffWeight m (cutoffPullback radius m (environment () ())))).sum := by
 induction members with
 | nil => rfl
 | cons m tail previous =>
  simp only [cutoffWord,Expr.eval,cutoffTerm,List.map_cons,List.sum_cons,previous]
  rfl


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
