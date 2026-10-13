import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCoupledPhysicalRFieldSource.Effect
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSectorEulerMixedSource.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCoupledPhysicalRFieldSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance coupledPhysicalMComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local notation "P" => burnolEvenAmbientProjection
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector

def actualProjectedCommonField (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=
 OriginalKCommonGapKernelSource.actualCommonFirst c • K c+
 OriginalKCommonGapKernelSource.actualCommonSecond c • Fphysical (K c)-
 OriginalKCommonGapKernelSource.actualCommonDeterminant c • G
def actualProjectedFourierCommonField (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=
 OriginalKCommonGapKernelSource.actualCommonSecond c • K c+
 OriginalKCommonGapKernelSource.actualCommonFirst c • Fphysical (K c)-
 OriginalKCommonGapKernelSource.actualCommonDeterminant c • Fphysical G

theorem actual_two_common_projected_input_fields (c : BurnolCompletedMellinCoordinate) :
 P (OriginalKCommonGapKernelSource.actualCommonField c)=actualProjectedCommonField c ∧
 P (OriginalKCommonGapKernelSource.actualFourierCommonField c)=actualProjectedFourierCommonField c :=by
 constructor
 · change P (actualProjectedCommonField c:BurnolL2)=actualProjectedCommonField c
   exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 · rw [(OriginalKCommonGapKernelSource.actual_Fourier_common_inventory c).1]
   change P (actualProjectedFourierCommonField c:BurnolL2)=actualProjectedFourierCommonField c
   exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self _

def actualProjectedMInputField (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolPaAmbientCarrier:=
 ((∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed c h x)*((c.value-1)⁻¹*2)) • actualProjectedCommonField c+
 ((∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed c h x)*(c.value⁻¹*2)) • actualProjectedFourierCommonField c

def actualWeightedMResponseField (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolPaAmbientCarrier:=
 actualResponseKappa c • actualProjectedMInputField c h+
 OriginalKFourierSectorRGramSource.actualFirstRWeight c h • actualWeightedKResponseField c+
 OriginalKFourierSectorRGramSource.actualSecondRWeight c h • actualWeightedFKResponseField c

/-- Complete original M consumes the generated whole weighted K/F K responses, retaining both original masses and all common source coefficients. -/
theorem actual_complete_weighted_M_source_field (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
 (actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c) •
 P (burnolDirectRightResolvent (c.value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))=
 actualWeightedMResponseField c h :=by
 have source:=congrArg (fun field:BurnolL2=>actualResponseKappa c • P field)
  (OriginalKCommonGapKernelSource.actual_common_M_R_source c h)
 unfold OriginalKCommonGapKernelSource.actualCommonMField at source
 dsimp only at source
 simp only [map_smul,map_add,smul_add] at source
 rw [(actual_two_common_projected_input_fields c).1,(actual_two_common_projected_input_fields c).2] at source
 change actualResponseKappa c • (OriginalKCommonGapKernelSource.actualCommonDeterminant c •
  P (burnolDirectRightResolvent (c.value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2)))=
 actualResponseKappa c • (((∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed c h x)*((c.value-1)⁻¹*2)) • actualProjectedCommonField c)+
 actualResponseKappa c • (((∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed c h x)*(c.value⁻¹*2)) • actualProjectedFourierCommonField c)+
 actualResponseKappa c • (OriginalKFourierSectorRGramSource.actualFirstRWeight c h •
  P (burnolDirectRightResolvent (c.value/2) (K c:BurnolL2)))+
 actualResponseKappa c • (OriginalKFourierSectorRGramSource.actualSecondRWeight c h •
  P (burnolDirectRightResolvent (c.value/2) (fourierL2 (K c:BurnolL2)))) at source
 rw [smul_comm (actualResponseKappa c) (OriginalKFourierSectorRGramSource.actualFirstRWeight c h),
  smul_comm (actualResponseKappa c) (OriginalKFourierSectorRGramSource.actualSecondRWeight c h),
  (actual_original_weighted_R_fields c).1,(actual_original_weighted_R_fields c).2] at source
 unfold actualWeightedMResponseField actualProjectedMInputField
 linear_combination (norm:=module) source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCoupledPhysicalRFieldSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
