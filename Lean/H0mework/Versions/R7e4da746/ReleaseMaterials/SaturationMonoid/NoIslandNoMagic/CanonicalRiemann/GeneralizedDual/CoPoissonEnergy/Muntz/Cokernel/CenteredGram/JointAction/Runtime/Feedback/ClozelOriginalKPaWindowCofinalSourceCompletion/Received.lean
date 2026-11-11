import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaWindowCofinalSourceCompletion.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaWindowCofinalSourceCompletion
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace R
export OriginalKWindowInverseResidualSourceAction (receivedResidualWindowDelta receivedResidualWindowTrace windowObservation received_window_effect)
end R
namespace F
export OriginalKFinitePaWindowOperatorSourceAction (Branches)
end F
namespace SF
export OriginalKWindowInverseResidualSourceAction.SF (Factory Packet)
end SF
namespace A
export OriginalKWindowInverseResidualSourceAction.A (Programme)
end A
namespace L
export OriginalKWindowInverseResidualSourceAction.L (Value groups)
end L
namespace C
export OriginalKFullSourceRAction.C (Value Var)
end C
local instance receivedCompletionGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var) (radius : ℝ) (source residual : F.Branches)

/-- The received current and its retained inverse fibre jointly recover the source window. -/
theorem received_current_with_residual (name : sourceCfg.LowVar ())
 (trace : type_of% (R.receivedResidualWindowTrace factory grade data sourceCfg language radius source residual name)) :
 burnolRadiusRestriction radius (OriginalKFullSourceRAction.originalField
  (R.receivedResidualWindowDelta factory grade data sourceCfg language radius source residual name)) +
 R.windowObservation radius residual = R.windowObservation radius source := by
 have generated := R.received_window_effect _ _ _ _ _ _ _ _ _ trace
 rw [sub_eq_iff_eq_add] at generated
 rw [generated]
 abel

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)

abbrev receivedCofinalWindow (stage : Nat) :=
 burnolRadiusRestriction (stage+1:ℝ) (OriginalKFullSourceRAction.originalField
  (R.receivedResidualWindowDelta (Residual.actualSourceFactory observation nontrivial half depth ordinal h)
   (Residual.actualSourcePacket observation nontrivial half depth ordinal h H N (stage+1:ℝ)).1
   (Residual.actualSourcePacket observation nontrivial half depth ordinal h H N (stage+1:ℝ)).2.1
   (Residual.actualSourcePacket observation nontrivial half depth ordinal h H N (stage+1:ℝ)).2.2.1
   (Residual.actualSourcePacket observation nontrivial half depth ordinal h H N (stage+1:ℝ)).2.2.2.down (stage+1:ℝ)
   (Residual.actualNu observation nontrivial half depth ordinal h H N)
   (Residual.actualReceivedResidual observation nontrivial half depth ordinal h H N (stage+1:ℝ))
   ((Residual.actualSourcePacket observation nontrivial half depth ordinal h H N (stage+1:ℝ)).2.2.2.down.symm ▸ ()))) +
 R.windowObservation (stage+1:ℝ) (Residual.actualReceivedResidual observation nontrivial half depth ordinal h H N (stage+1:ℝ))

theorem received_cofinal_window_source (stage : Nat)
 (trace : type_of% (R.receivedResidualWindowTrace (Residual.actualSourceFactory observation nontrivial half depth ordinal h)
  (Residual.actualSourcePacket observation nontrivial half depth ordinal h H N (stage+1:ℝ)).1
  (Residual.actualSourcePacket observation nontrivial half depth ordinal h H N (stage+1:ℝ)).2.1
  (Residual.actualSourcePacket observation nontrivial half depth ordinal h H N (stage+1:ℝ)).2.2.1
  (Residual.actualSourcePacket observation nontrivial half depth ordinal h H N (stage+1:ℝ)).2.2.2.down (stage+1:ℝ)
  (Residual.actualNu observation nontrivial half depth ordinal h H N)
  (Residual.actualReceivedResidual observation nontrivial half depth ordinal h H N (stage+1:ℝ))
  ((Residual.actualSourcePacket observation nontrivial half depth ordinal h H N (stage+1:ℝ)).2.2.2.down.symm ▸ ()))) :
 receivedCofinalWindow observation nontrivial half depth ordinal h H N stage =
 windowRead stage (actualPaSource observation nontrivial half depth ordinal h H N) := by
 have generated := received_current_with_residual _ _ _ _ _ _ _ _ _ trace
 change receivedCofinalWindow observation nontrivial half depth ordinal h H N stage =
  R.windowObservation (stage+1:ℝ) (Residual.actualNu observation nontrivial half depth ordinal h H N) at generated
 have origin : Residual.actualNu observation nontrivial half depth ordinal h H N =
  OriginalKBoundaryNativeSourceAction.sourceFields (sourceNu (actualPaSource observation nontrivial half depth ordinal h H N)) :=
  actual_source_nu_receipt _ _ _ _ _ _ _ _
 rw [origin] at generated
 simpa only [OriginalKWindowInverseResidualSourceAction.windowObservation,windowRead,ContinuousLinearMap.comp_apply,
  OriginalKBoundaryNativeSourceAction.source_fields_first] using generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaWindowCofinalSourceCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
