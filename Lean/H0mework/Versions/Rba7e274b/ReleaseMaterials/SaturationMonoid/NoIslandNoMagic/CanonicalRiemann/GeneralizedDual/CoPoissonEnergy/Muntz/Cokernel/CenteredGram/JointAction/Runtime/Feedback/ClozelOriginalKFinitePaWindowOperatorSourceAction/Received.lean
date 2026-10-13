import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Born
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
local instance receivedFiniteGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)
variable (radius : ℝ) (source : Branches)

def receivedWindowDelta (name : sourceCfg.LowVar ()) : Branches :=
 CF.collapseValue grade ((finiteStockBorn factory grade data sourceCfg language radius source).activeEnvironment () name) -
 CF.collapseValue grade (finiteStockUpdatedValue factory grade data sourceCfg language radius source)

def receivedWindowTrace (name : sourceCfg.LowVar ()) :
 Trace (windowEnvironment source) (completeWindowWord radius)
  (.const (receivedWindowDelta factory grade data sourceCfg language radius source name)) := by
 unfold receivedWindowDelta
 rw [finite_stock_generated_source_delta]
 exact finiteWindowTrace radius source

def receivedFirstInverseResidual (name : sourceCfg.LowVar ()) : BurnolL2 :=
 OriginalKFullSourceRAction.originalField source - burnolMobiusSourceL2
  (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField
   (receivedWindowDelta factory grade data sourceCfg language radius source name)))

theorem received_inverse_residual_source (name : sourceCfg.LowVar ())
 (write : type_of% (finite_stock_generated_source_delta factory grade data sourceCfg language radius source name)) :
 receivedFirstInverseResidual factory grade data sourceCfg language radius source name = firstInverseResidual radius source := by
 unfold receivedFirstInverseResidual receivedWindowDelta
 rw [write]
 rfl

theorem received_full_window (name : sourceCfg.LowVar ())
 (trace : type_of% (receivedWindowTrace factory grade data sourceCfg language radius source name)) :
 burnolRadiusRestriction radius (OriginalKFullSourceRAction.originalField
  (receivedWindowDelta factory grade data sourceCfg language radius source name)) =
 burnolSourceOnlyCoPoissonWindow radius (OriginalKFullSourceRAction.originalField source) :=
 window_from_received_trace radius source _ trace

theorem received_stock_update_cochain (name : sourceCfg.LowVar ())
 (write : type_of% (finite_stock_generated_source_delta factory grade data sourceCfg language radius source name)) :
 (SourceOperationExecution.Cochain.expression (Finsupp.single (sourceStockWord radius source) (1:ℤ))).eval
  (mixedEnvironment
   (windowEnvironment (CF.collapseValue grade (finiteStockUpdatedValue factory grade data sourceCfg language radius source)))
   (windowEnvironment (receivedWindowDelta factory grade data sourceCfg language radius source name))) = 0 := by
 unfold receivedWindowDelta
 rw [write]
 exact SourceOperationExecution.Cochain.source_zero _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
