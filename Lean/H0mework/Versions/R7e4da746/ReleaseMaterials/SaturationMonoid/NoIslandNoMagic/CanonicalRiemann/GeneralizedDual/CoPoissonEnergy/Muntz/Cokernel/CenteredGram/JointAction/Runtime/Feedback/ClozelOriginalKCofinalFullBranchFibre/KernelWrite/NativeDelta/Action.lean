import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open BurnolPhysicalState SourceGeneratedScalarDifferentialResidual SourceOperationScalarInventoryLift
open scoped InnerProductSpace Topology
namespace P
export OriginalKCombPhysicalAction (R value)
end P
namespace D
export OriginalKCombFirstFullSourceDynamics (raw raw_successor original_xi_value)
end D
namespace Div
export OriginalKDirectRCofinalDivision (sourceResponse source_response_value source_response_positionGap actual_R_source_split)
end Div
namespace Pa
export OriginalKCombCofinalPaAction (actualPa actualPa_mem invisible E)
end Pa
namespace SourceGap
export OriginalKCombCofinalRAction (actual_source_gap original_R_direct parameter_rightQuarter)
end SourceGap
namespace Pricing
export BurnolPhysicalState.CombSource.Pricing (ambient_R_positionGap)
end Pricing
local instance deltaComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance actionGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def physicalIncrement : BurnolL2 :=
 (incrementInput observation nontrivial half depth ordinal).1+(incrementInput observation nontrivial half depth ordinal).2

def inverseBranches := NativeSigma.collapseNative (NativeSigma.originalFactory observation nontrivial half)
 (NativeSigma.originalPacket observation nontrivial half depth ordinal)
 (NativeSigma.originalInverse observation nontrivial half depth ordinal).val

def inverseTotal : BurnolL2 :=
 ((inverseBranches observation nontrivial half depth ordinal).1.1+(inverseBranches observation nontrivial half depth ordinal).1.2)+
 ((inverseBranches observation nontrivial half depth ordinal).2.1+(inverseBranches observation nontrivial half depth ordinal).2.2)

theorem actual_inverse_branches : inverseBranches observation nontrivial half depth ordinal=
 Full.branches observation nontrivial half (incrementInput observation nontrivial half depth ordinal) :=
 NativeSigma.original_native_sigma_inverse observation nontrivial half depth ordinal

private theorem branches_readback (source : BurnolL2×BurnolL2) :
 branchReadback observation nontrivial half (Full.branches observation nontrivial half source)=source :=
 source_branches_readback observation nontrivial half source

/-- The independent full branch inverse recovers both actual source-increment coordinates. -/
theorem actual_inverse_source_readback :
 branchReadback observation nontrivial half (inverseBranches observation nontrivial half depth ordinal)=
 incrementInput observation nontrivial half depth ordinal :=
 (congrArg (branchReadback observation nontrivial half)
  (actual_inverse_branches observation nontrivial half depth ordinal)).trans
  (branches_readback observation nontrivial half _)

/-- This is the existing native range inverse, before any scalar or projected read. -/
theorem actual_inverse_total : inverseTotal observation nontrivial half depth ordinal=
 P.R observation nontrivial half (physicalIncrement observation nontrivial half depth ordinal) :=
 (Full.complete_of_branches observation nontrivial half _ _
  (actual_inverse_branches observation nontrivial half depth ordinal)).2.2.1

theorem actual_increment_raw : physicalIncrement observation nontrivial half depth (ordinal+1)=
 D.raw observation nontrivial half depth (ordinal+1)-D.raw observation nontrivial half depth ordinal := by
 have generated:=congrArg (fun pair : BurnolL2×BurnolL2=>pair.1+pair.2)
  (actual_increment_successor observation nontrivial half depth ordinal)
 change _=(D.input observation nontrivial half depth (ordinal+1)).1+
  (D.input observation nontrivial half depth (ordinal+1)).2-
  ((D.input observation nontrivial half depth ordinal).1+(D.input observation nontrivial half depth ordinal).2)
 exact generated.trans (by simp only [Prod.fst_sub,Prod.snd_sub]; abel)

theorem actual_inverse_successor : inverseTotal observation nontrivial half depth (ordinal+1)=
 D.raw observation nontrivial half depth (ordinal+2)-D.raw observation nontrivial half depth (ordinal+1) := by
 rw [actual_inverse_total,actual_increment_raw,map_sub,←D.raw_successor,←D.raw_successor]

theorem actual_increment_positionGap : physicalIncrement observation nontrivial half depth (ordinal+1)∈
 locallyConstantFace burnolUnscaledCommonGapRadius := by
 rw [actual_increment_raw]
 exact (locallyConstantFace burnolUnscaledCommonGapRadius).sub_mem
  (SourceGap.actual_source_gap observation nontrivial half depth (ordinal+1))
  (SourceGap.actual_source_gap observation nontrivial half depth ordinal)

private theorem invisible_sub (left right : BurnolL2) : Pa.invisible (left-right)=Pa.invisible left-Pa.invisible right := by
 unfold Pa.invisible
 rw [map_sub]
 change (left-right)-((Pa.E left:BurnolL2)-(Pa.E right:BurnolL2))=
  (left-(Pa.E left:BurnolL2))-(right-(Pa.E right:BurnolL2))
 abel

def responseDifference : BurnolPaAmbientCarrier :=
 Div.sourceResponse observation nontrivial half depth (ordinal+1)-Div.sourceResponse observation nontrivial half depth ordinal

theorem response_difference_positionGap : (responseDifference observation nontrivial half depth ordinal : BurnolL2)∈
 locallyConstantFace burnolUnscaledCommonGapRadius :=
 (locallyConstantFace burnolUnscaledCommonGapRadius).sub_mem
  (Div.source_response_positionGap observation nontrivial half depth (ordinal+1))
  (Div.source_response_positionGap observation nontrivial half depth ordinal)

def actualPaDifference : BurnolPaAmbientCarrier :=
 Pa.actualPa observation nontrivial half depth (ordinal+1)-Pa.actualPa observation nontrivial half depth ordinal

theorem actual_pa_difference_mem : actualPaDifference observation nontrivial half depth ordinal∈burnolCompactCoPoissonClosedRange :=
 burnolCompactCoPoissonClosedRange.toSubmodule.sub_mem
  (Pa.actualPa_mem observation nontrivial half depth (ordinal+1)) (Pa.actualPa_mem observation nontrivial half depth ordinal)

/-- Existing physical Division acts on the actual Pa source difference, with no qualification premise. -/
theorem actual_division_response :
 burnolPaResolventPhysicalResponse observation nontrivial half.down
  (actualPaDifference observation nontrivial half depth ordinal)
  (actual_pa_difference_mem observation nontrivial half depth ordinal)=
 responseDifference observation nontrivial half depth ordinal := by
 apply Subtype.ext
 change burnolDirectRightResolvent (observation.coordinate/2)
  ((Pa.actualPa observation nontrivial half depth (ordinal+1):BurnolL2)-
   (Pa.actualPa observation nontrivial half depth ordinal:BurnolL2))=_
 rw [←SourceGap.original_R_direct,map_sub,←Div.source_response_value,←Div.source_response_value]
 rfl

def incrementPa : BurnolPaAmbientCarrier := Pa.E (physicalIncrement observation nontrivial half depth ordinal)

theorem increment_pa_mem : incrementPa observation nontrivial half depth ordinal∈burnolCompactCoPoissonClosedRange :=
 Submodule.starProjection_apply_mem _ _

def incrementResponse : BurnolPaAmbientCarrier :=
 burnolPaResolventPhysicalResponse observation nontrivial half.down
  (incrementPa observation nontrivial half depth ordinal) (increment_pa_mem observation nontrivial half depth ordinal)

theorem increment_response_value : (incrementResponse observation nontrivial half depth ordinal:BurnolL2)=
 P.R observation nontrivial half (incrementPa observation nontrivial half depth ordinal:BurnolL2) := by
 rw [SourceGap.original_R_direct]
 rfl

theorem increment_response_positionGap : (incrementResponse observation nontrivial half depth ordinal:BurnolL2)∈
 locallyConstantFace burnolUnscaledCommonGapRadius :=
 (incrementResponse observation nontrivial half depth ordinal).property.1.1

/-- The first native occurrence and all successors use their own actual complete increment. -/
theorem actual_inverse_physical_split : inverseTotal observation nontrivial half depth ordinal=
 (incrementResponse observation nontrivial half depth ordinal:BurnolL2)+
 P.R observation nontrivial half (Pa.invisible (physicalIncrement observation nontrivial half depth ordinal)) := by
 rw [actual_inverse_total,increment_response_value]
 unfold Pa.invisible incrementPa
 rw [map_sub]
 abel

theorem actual_increment_pa : incrementPa observation nontrivial half depth (ordinal+1)=
 actualPaDifference observation nontrivial half depth ordinal := by
 unfold incrementPa
 rw [actual_increment_raw,map_sub]
 rfl

/-- Qualification and the old Division response are identified by the same generated source difference. -/
theorem actual_increment_response : incrementResponse observation nontrivial half depth (ordinal+1)=
 responseDifference observation nontrivial half depth ordinal := by
 apply Subtype.ext
 have responseValue : (responseDifference observation nontrivial half depth ordinal:BurnolL2)=
  P.R observation nontrivial half (actualPaDifference observation nontrivial half depth ordinal:BurnolL2) := by
  rw [←actual_division_response,SourceGap.original_R_direct]
  rfl
 exact (increment_response_value observation nontrivial half depth (ordinal+1)).trans
  ((congrArg (fun source : BurnolPaAmbientCarrier=>P.R observation nontrivial half (source:BurnolL2))
    (actual_increment_pa observation nontrivial half depth ordinal)).trans responseValue.symm)

/-- The actual native residual is calculated by qualified Division plus the complete invisible difference. -/
theorem actual_inverse_division_split : inverseTotal observation nontrivial half depth (ordinal+1)=
 (responseDifference observation nontrivial half depth ordinal:BurnolL2)+
 P.R observation nontrivial half (Pa.invisible (physicalIncrement observation nontrivial half depth (ordinal+1))) := by
 rw [actual_inverse_successor,actual_increment_raw,invisible_sub,map_sub]
 have source:=congrArg₂ (fun left right : BurnolL2=>left-right)
  (Div.actual_R_source_split observation nontrivial half depth (ordinal+1))
  (Div.actual_R_source_split observation nontrivial half depth ordinal)
 exact source.trans (by change (_+_)-(_+_)=(_-_)+(_-_); abel)

/-- The next R action keeps its entire R-squared invisible contribution. -/
theorem actual_inverse_R2 : P.R observation nontrivial half (inverseTotal observation nontrivial half depth (ordinal+1))=
 P.R observation nontrivial half (responseDifference observation nontrivial half depth ordinal:BurnolL2)+
 P.R observation nontrivial half (P.R observation nontrivial half
  (Pa.invisible (physicalIncrement observation nontrivial half depth (ordinal+1)))) := by
 rw [actual_inverse_division_split,map_add]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
