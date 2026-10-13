import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWindowInverseResidualSourceAction.Whole
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



local instance residualReceivedGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var) (radius : ℝ) (source residual : F.Branches)

def receivedResidualWindowDelta (name : sourceCfg.LowVar ()) : F.Branches :=
 CF.collapseValue grade ((residualStockBorn factory grade data sourceCfg language radius source residual).activeEnvironment () name) -
 CF.collapseValue grade (residualStockUpdatedValue factory grade data sourceCfg language radius source residual)

def receivedResidualWindowTrace (name : sourceCfg.LowVar ()) :
 Trace (F.windowEnvironment source) (residualWindowCode radius source residual)
  (.const (receivedResidualWindowDelta factory grade data sourceCfg language radius source residual name)) := by
 unfold receivedResidualWindowDelta
 rw [residual_stock_generated_source_delta]
 exact residualWindowTrace _ _ _

theorem received_window_effect (name : sourceCfg.LowVar ())
 (trace : type_of% (receivedResidualWindowTrace factory grade data sourceCfg language radius source residual name)) :
 burnolRadiusRestriction radius (OriginalKFullSourceRAction.originalField
  (receivedResidualWindowDelta factory grade data sourceCfg language radius source residual name)) - windowObservation radius source =
 -windowObservation radius residual := residual_window_from_received_trace _ _ _ _ trace

theorem received_window_full_source (name : sourceCfg.LowVar ())
 (write : type_of% (residual_stock_generated_source_delta factory grade data sourceCfg language radius source residual name)) :
 receivedResidualWindowDelta factory grade data sourceCfg language radius source residual name =
 Native.sourceFields (burnolRadiusZeroExtension radius (windowObservation radius (source-residual))) := by
 unfold receivedResidualWindowDelta
 rw [write,residual_window_source_value]

theorem received_residual_cochain (name : sourceCfg.LowVar ())
 (write : type_of% (residual_stock_generated_source_delta factory grade data sourceCfg language radius source residual name)) :
 (SourceOperationExecution.Cochain.expression (Finsupp.single (residualStockCode radius source residual) (1:ℤ))).eval
  (mixedEnvironment
   (F.windowEnvironment (CF.collapseValue grade (residualStockUpdatedValue factory grade data sourceCfg language radius source residual)))
   (F.windowEnvironment (receivedResidualWindowDelta factory grade data sourceCfg language radius source residual name))) = 0 := by
 unfold receivedResidualWindowDelta
 rw [write]
 exact SourceOperationExecution.Cochain.source_zero _ _ _

variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))

theorem consume_residual_source_receipt {Target : Prop}
 (consumer : (whole : type_of% (residualWholeAt factory packet radius source residual)) →
 (write : type_of% (residual_stock_generated_source_delta factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source residual (packet.2.2.2.down.symm ▸ ()))) →
 (trace : type_of% (receivedResidualWindowTrace factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source residual (packet.2.2.2.down.symm ▸ ()))) → Target) : Target :=
 consumer (residualWholeAt _ _ _ _ _)
 (residual_stock_generated_source_delta _ _ _ _ _ _ _ _ _)
 (receivedResidualWindowTrace _ _ _ _ _ _ _ _ _)

theorem received_residual_whole_window :
 ∃ whole : type_of% (residualWholeAt factory packet radius source residual),
 (type_of% whole.actual_step) ∧ (type_of% whole.same_ledger) ∧ (type_of% whole.same_visit) ∧ (type_of% whole.entry) ∧
 (type_of% whole.whole_destination) ∧ (type_of% whole.source_environment) ∧ (type_of% whole.source_expression) ∧
 (type_of% (received_window_effect factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source residual
  (packet.2.2.2.down.symm ▸ ()) (receivedResidualWindowTrace _ _ _ _ _ _ _ _ _))) ∧
 (type_of% (received_window_full_source factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source residual
  (packet.2.2.2.down.symm ▸ ()) (residual_stock_generated_source_delta _ _ _ _ _ _ _ _ _))) ∧
 (type_of% (received_residual_cochain factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source residual
  (packet.2.2.2.down.symm ▸ ()) (residual_stock_generated_source_delta _ _ _ _ _ _ _ _ _))) := by
 exact consume_residual_source_receipt factory radius source residual packet fun whole write trace =>
  ⟨whole,whole.actual_step,whole.same_ledger,whole.same_visit,whole.entry,whole.whole_destination,
   whole.source_environment,whole.source_expression,received_window_effect _ _ _ _ _ _ _ _ _ trace,
   received_window_full_source _ _ _ _ _ _ _ _ _ write,received_residual_cochain _ _ _ _ _ _ _ _ _ write⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWindowInverseResidualSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
