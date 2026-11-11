import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaWindowCofinalSourceCompletion.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaWindowCofinalSourceCompletion
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open MeasureTheory Set
open scoped InnerProductSpace


open CategoryTheory
open Filter
open scoped Topology
namespace Scalar
export SourceGeneratedScalarCofinalKernelCompletion (Data)
end Scalar

def sourceData : Scalar.Data (R:=ℂ) (Generator:=PaSourceCarrier)
 (Carrier:=fun stage : Nat => BurnolRadiusIntervalL2 (stage+1:ℝ)) where
 evaluator stage := (windowRead stage).toLinearMap
 transition stage := (windowTransition stage).toLinearMap

theorem source_data_compatible : sourceData.Compatible := by
 intro stage
 apply LinearMap.ext
 intro value
 exact source_window_transition stage value

theorem source_data_kernel_separated : sourceData.KernelSeparated := by
 intro value invisible
 have restrictions (stage : Nat) : burnolRadiusRestriction (stage+1:ℝ) ((value : BurnolPaAmbientCarrier) : BurnolL2) = 0 := by
  rw [←source_window_read]
  exact invisible stage
 have cutoffs (stage : Nat) : OriginalKPaCutoffCompressionSourceAction.cutoffAction (stage+1:ℝ)
  ((value : BurnolPaAmbientCarrier) : BurnolL2) = 0 := by
  change burnolRadiusZeroExtension (stage+1:ℝ) (burnolRadiusRestriction (stage+1:ℝ)
   ((value : BurnolPaAmbientCarrier) : BurnolL2)) = 0
  rw [restrictions,map_zero]
 have normIdentity (stage : Nat) :
  ‖OriginalKPaCutoffCompressionSourceAction.outsideTailAction (stage+1:ℝ)
   ((value : BurnolPaAmbientCarrier) : BurnolL2)‖ = ‖value‖ := by
  change ‖((value : BurnolPaAmbientCarrier) : BurnolL2)-
   OriginalKPaCutoffCompressionSourceAction.cutoffAction (stage+1:ℝ)
    ((value : BurnolPaAmbientCarrier) : BurnolL2)‖ = ‖value‖
  rw [cutoffs,sub_zero]
  rfl
 have strong := OriginalKPaCutoffCompressionSourceAction.outside_tail_norm_tendsto
  ((value : BurnolPaAmbientCarrier) : BurnolL2)
 have allzero : Tendsto (fun _ : Nat => ‖value‖) atTop (𝓝 0) :=
  strong.congr normIdentity
 have zero : ‖value‖=0 := tendsto_nhds_unique tendsto_const_nhds allzero
 exact norm_eq_zero.mp zero

def sourceCompletion := sourceData.Completion source_data_compatible

def sourceCompletionMap := sourceData.completionMap source_data_compatible

theorem source_completion_map_injective : Function.Injective sourceCompletionMap :=
 sourceData.completionMap_injective source_data_compatible source_data_kernel_separated

theorem source_completion_window_readback (stage : Nat) : type_of%
 (sourceData.source_to_evaluator source_data_compatible stage) :=
 sourceData.source_to_evaluator source_data_compatible stage

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaWindowCofinalSourceCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
