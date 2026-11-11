import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRSourceSuccessor.Whole
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
local instance receivedPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance receivedSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)
variable (producer : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

/-- The actor part is read from the actual material effect after paying its full inherited R cost. -/
def receivedOwnR := CF.collapseValue (grade+1)
 ((rMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).raw.effect
  (rMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).environment
  (rMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).increment) -
 FullR.variableAction observation nontrivial half
  (inheritedSourceIncrement observation nontrivial half depth ordinal h H N producer grade data sourceCfg language (language.symm ▸ ()))

theorem received_material_own_R
 (effect : type_of% (actual_material_R_effect observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) :
 receivedOwnR observation nontrivial half depth ordinal h H N producer grade data sourceCfg language =
 ownSourceR observation nontrivial half depth ordinal h H N := by
 unfold receivedOwnR
 rw [effect]
 abel

theorem received_own_R_physical
 (effect : type_of% (actual_material_R_effect observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) :
 (receivedOwnR observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).1.1 ∈
 evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
 rw [received_material_own_R _ _ _ _ _ _ _ _ _ _ _ _ _ effect]
 exact own_source_R_physical _ _ _ _ _ _ _ _

theorem received_own_R_positionGap
 (effect : type_of% (actual_material_R_effect observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) :
 (receivedOwnR observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).1.1 ∈
 locallyConstantFace burnolUnscaledCommonGapRadius :=
 (received_own_R_physical _ _ _ _ _ _ _ _ _ _ _ _ _ effect).1.1

def receivedPhysicalR : BurnolPaAmbientCarrier :=
 ⟨(receivedOwnR observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).1.1,
  received_own_R_physical _ _ _ _ _ _ _ _ _ _ _ _ _ (actual_material_R_effect _ _ _ _ _ _ _ _ _ _ _ _ _)⟩

theorem received_physical_source_response
 (effect : type_of% (actual_material_R_effect observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) :
 receivedPhysicalR observation nontrivial half depth ordinal h H N producer grade data sourceCfg language =
 burnolPaResolventPhysicalResponse observation nontrivial
  (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf
  (decodedPaSource observation nontrivial half depth ordinal h H N).val
  (decoded_pa_source_qualified observation nontrivial half depth ordinal h H N) := by
 apply Subtype.ext
 change (receivedOwnR observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).1.1 = _
 rw [received_material_own_R _ _ _ _ _ _ _ _ _ _ _ _ _ effect,own_source_R_read,OriginalKCombCofinalRAction.original_R_direct]
 rfl

/-- The independent physical reader now consumes the actual material portion and its own source unit coefficient. -/
theorem received_own_R_unit_rank
 (effect : type_of% (actual_material_R_effect observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)) :
 burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (receivedPhysicalR observation nontrivial half depth ordinal h H N producer grade data sourceCfg language) =
 burnolPaResolventSourceCoefficient
  (burnolDivisionZeroCompletedMellinCoordinate observation (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf)
  (decodedPaSource observation nontrivial half depth ordinal h H N).val •
 burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (burnolZeroOwnedUnitTailState observation nontrivial (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf) := by
 rw [received_physical_source_response _ _ _ _ _ _ _ _ _ _ _ _ _ effect]
 exact burnolPaResolventPhysicalResponse_Q _ _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
