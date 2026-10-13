import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Born
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open BurnolPhysicalState

theorem source_window_from_received_trace (source : D.SourceBranches) (endpoint : D.SourceBranches)
 (trace : Trace (sourcePaEnvironment source) sourcePaCode (.const endpoint)) (radius : ℝ) :
 burnolSourceOnlyCoPoissonWindow radius (OriginalKFullSourceRAction.originalField endpoint) =
 burnolRadiusRestriction radius (OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField source) : BurnolL2) := by
 have action := trace.sound
 change sourcePaSourceAction source=endpoint at action
 rw [←action]
 change burnolSourceOnlyCoPoissonWindow radius (OriginalKFullSourceRAction.originalField (Native.sourceFields (sourcePaMobius source))) = _
 rw [Native.source_fields_first]
 exact source_pa_window_generated radius source

local instance paTraceGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)
variable (source : D.SourceBranches)

def actual_born_delta_source_trace (name : sourceCfg.LowVar ()) :
 Trace (sourcePaEnvironment source) sourcePaCode
  (.const (CF.collapseValue grade ((paStockBorn factory grade data sourceCfg language source).activeEnvironment () name) -
   CF.collapseValue grade (paStockUpdatedValue factory grade data sourceCfg language source))) := by
 rw [pa_stock_generated_source_delta]
 exact sourcePaTrace source

theorem actual_born_window_from_source_trace (name : sourceCfg.LowVar ()) (radius : ℝ) :
 type_of% (pa_stock_source_window factory grade data sourceCfg language source name radius) :=
 source_window_from_received_trace source _ (actual_born_delta_source_trace factory grade data sourceCfg language source name) radius

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
