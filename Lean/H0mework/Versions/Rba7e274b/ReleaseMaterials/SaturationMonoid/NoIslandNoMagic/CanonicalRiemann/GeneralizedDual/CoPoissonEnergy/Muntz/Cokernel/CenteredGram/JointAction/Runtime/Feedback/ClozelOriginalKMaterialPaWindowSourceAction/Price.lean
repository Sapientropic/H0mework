import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Born
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
local instance paPriceComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance paPriceGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)
variable (source : D.SourceBranches)

def receivedPaSource (name : sourceCfg.LowVar ()) : BurnolL2 :=
 OriginalKFullSourceRAction.originalField
 (CF.collapseValue grade ((paStockBorn factory grade data sourceCfg language source).activeEnvironment () name) -
  CF.collapseValue grade (paStockUpdatedValue factory grade data sourceCfg language source))

theorem received_source_is_own_Mobius (name : sourceCfg.LowVar ())
 (write : type_of% (pa_stock_generated_source_delta factory grade data sourceCfg language source name)) :
 receivedPaSource factory grade data sourceCfg language source name = sourcePaMobius source := by
 unfold receivedPaSource
 rw [write]
 exact Native.source_fields_first _

theorem received_window_price (name : sourceCfg.LowVar ())
 (write : type_of% (pa_stock_generated_source_delta factory grade data sourceCfg language source name)) (radius : ℝ) :
 burnolSourceOnlyCoPoissonWindow radius (receivedPaSource factory grade data sourceCfg language source name) =
 burnolRadiusRestriction radius (OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField source) : BurnolL2) := by
 rw [received_source_is_own_Mobius factory grade data sourceCfg language source name write]
 exact source_pa_window_generated radius source

theorem received_two_mean_prices (name : sourceCfg.LowVar ())
 (write : type_of% (pa_stock_generated_source_delta factory grade data sourceCfg language source name)) :
 burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
  (OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField source)) =
  (-1/2:ℂ) * burnolSourceWindowIntegral
   (burnolTateReciprocalL2 (receivedPaSource factory grade data sourceCfg language source name)) ∧
 burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField source))) =
  (-1/2:ℂ) * burnolSourceWindowIntegral (receivedPaSource factory grade data sourceCfg language source name) := by
 rw [received_source_is_own_Mobius factory grade data sourceCfg language source name write]
 exact source_pa_two_means source

theorem received_moving_mean_price (name : sourceCfg.LowVar ())
 (write : type_of% (pa_stock_generated_source_delta factory grade data sourceCfg language source name)) (t : ℝ) :
 FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
  (OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField source) : BurnolL2)) =
 OriginalKQBSourceWindowAction.paSourceMovingMean (receivedPaSource factory grade data sourceCfg language source name) t := by
 rw [received_source_is_own_Mobius factory grade data sourceCfg language source name write]
 exact OriginalKQBSourceWindowAction.pa_source_window_read _ (source_pa_qualified source) t

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
