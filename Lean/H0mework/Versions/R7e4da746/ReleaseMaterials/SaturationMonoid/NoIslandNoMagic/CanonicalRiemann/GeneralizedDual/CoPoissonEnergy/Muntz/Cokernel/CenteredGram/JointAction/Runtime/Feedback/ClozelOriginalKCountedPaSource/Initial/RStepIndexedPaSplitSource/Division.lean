import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceResidualRNativeSuccessor.Projection

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.RStepIndexedPaSplitSource
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CenteredGram.IntegralGraphJointAction
namespace Split
export OriginalKSourceResidualRNativeSuccessor
 (SourceBranches sourcePaField sourcePaInput sourceNonPaInput source_Pa_qualified source_Pa_nonPa_sum)
end Split

namespace Division
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (input:Split.SourceBranches)
local instance paComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def paSource : BurnolPaAmbientCarrier :=
 OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField input)
theorem qualified : paSource input∈burnolCompactCoPoissonClosedRange := Split.source_Pa_qualified input
def pa := OriginalKFullSourceRAction.variableAction observation nontrivial half (Split.sourcePaInput input)
def nonPa := OriginalKFullSourceRAction.variableAction observation nontrivial half (Split.sourceNonPaInput input)
theorem pa_physical : (pa observation nontrivial half input).1.1∈
 evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
 change OriginalKCombPhysicalAction.R observation nontrivial half (paSource input:BurnolL2)∈_
 rw [OriginalKCombCofinalRAction.original_R_direct]
 exact burnolPaResolvent_physical observation nontrivial
  (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf _ (qualified input)
theorem pa_gap : (pa observation nontrivial half input).1.1∈locallyConstantFace burnolUnscaledCommonGapRadius :=
 (pa_physical observation nontrivial half input).1.1
def paPhysical : BurnolPaAmbientCarrier :=
 ⟨(pa observation nontrivial half input).1.1,pa_physical observation nontrivial half input⟩
theorem pa_response : paPhysical observation nontrivial half input=
 burnolPaResolventPhysicalResponse observation nontrivial
  (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf
  (paSource input) (qualified input) := by
 apply Subtype.ext
 change OriginalKCombPhysicalAction.R observation nontrivial half (paSource input:BurnolL2)=_
 rw [OriginalKCombCofinalRAction.original_R_direct]
 rfl
theorem pa_unit_rank : burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
 (paPhysical observation nontrivial half input)=
 burnolPaResolventSourceCoefficient
  (burnolDivisionZeroCompletedMellinCoordinate observation
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf)
  (paSource input) •
 burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (burnolZeroOwnedUnitTailState observation nontrivial
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf) := by
 rw [pa_response]
 exact burnolPaResolventPhysicalResponse_Q _ _ _ _ _
theorem sum : OriginalKFullSourceRAction.variableAction observation nontrivial half input=
 pa observation nontrivial half input+nonPa observation nontrivial half input := by
 exact (congrArg (OriginalKFullSourceRAction.variableAction observation nontrivial half)
  (Split.source_Pa_nonPa_sum input)).symm.trans (map_add _ _ _)
theorem outside :
 (OriginalKFullSourceRAction.variableAction observation nontrivial half input).1.1-
  (burnolEvenAmbientProjection (OriginalKFullSourceRAction.variableAction observation nontrivial half input).1.1:BurnolL2)=
 (nonPa observation nontrivial half input).1.1-
  (burnolEvenAmbientProjection (nonPa observation nontrivial half input).1.1:BurnolL2) := by
 have physical:(burnolEvenAmbientProjection (pa observation nontrivial half input).1.1:BurnolL2)=
  (pa observation nontrivial half input).1.1 := Submodule.starProjection_eq_self_iff.mpr (pa_physical observation nontrivial half input)
 rw [sum]
 simp only [Prod.fst_add,map_add,Submodule.coe_add]
 rw [physical]
 abel
end Division
run_cmd IO.eprintln "PaSplit: source generated Pa qualification, original Division/Q unit and full nonPa outside reached"


end CountedPaInitial.RStepIndexedPaSplitSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
