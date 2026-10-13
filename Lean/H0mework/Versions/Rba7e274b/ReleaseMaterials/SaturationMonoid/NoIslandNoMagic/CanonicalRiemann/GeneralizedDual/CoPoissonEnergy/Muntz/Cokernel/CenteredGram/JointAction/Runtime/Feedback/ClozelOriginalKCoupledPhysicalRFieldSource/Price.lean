import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCoupledPhysicalRFieldSource.MSource
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
local instance coupledPhysicalPriceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local notation "P" => burnolEvenAmbientProjection

/-- The complete physical weighted M field is consumed by the receiver's own physical reader. -/
theorem actual_complete_weighted_M_field_price (c : BurnolCompletedMellinCoordinate) (h : ℝ)
 (physical : BurnolPaAmbientCarrier) :
 actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c*
 inner ℂ (physical:BurnolL2)
  (burnolDirectRightResolvent (c.value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))=
 inner ℂ physical (actualWeightedMResponseField c h) :=by
 have source:=congrArg (inner ℂ physical) (actual_complete_weighted_M_source_field c h)
 rw [inner_smul_right] at source
 have read:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  |>.inner_orthogonalProjectionOnto_eq_of_mem_left physical
   (burnolDirectRightResolvent (c.value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))
 change inner ℂ physical (P (burnolDirectRightResolvent (c.value/2)
  (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2)))=
 inner ℂ (physical:BurnolL2) (burnolDirectRightResolvent (c.value/2)
  (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2)) at read
 rw [read] at source
 exact source

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualWeightedKMeanPrice (h : ℝ) : ℂ:=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 inner ℂ (K c) (actualWeightedMResponseField c h)
def actualWeightedFKMeanPrice (h : ℝ) : ℂ:=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 inner ℂ (Fphysical (K c)) (actualWeightedMResponseField c h)

/-- Original M's two prices consume the complete source-generated whole field, with both old unweighted prices retained by the independent consumer. -/
theorem actual_complete_weighted_sector_M_prices (h : ℝ) :
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 actualResponseKappa c*OriginalKSectorEulerMixedSource.actualCoupledKMeanPrice observation nontrivial half h=
 actualWeightedKMeanPrice observation nontrivial half h ∧
 actualResponseKappa c*OriginalKSectorEulerMixedSource.actualCoupledFKMeanPrice observation nontrivial half h=
 actualWeightedFKMeanPrice observation nontrivial half h :=by
 dsimp only
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have Kprice:=OriginalKCommonGapKernelSource.actual_common_M_source_price c h (K c)
 have FKprice:=OriginalKCommonGapKernelSource.actual_common_M_source_price c h (Fphysical (K c))
 change OriginalKCommonGapKernelSource.actualCommonDeterminant c*inner ℂ (K c:BurnolL2)
  (burnolDirectRightResolvent (c.value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))=
  OriginalKCommonGapKernelSource.actualCommonKMeanPrice observation nontrivial half h at Kprice
 change OriginalKCommonGapKernelSource.actualCommonDeterminant c*inner ℂ (Fphysical (K c):BurnolL2)
  (burnolDirectRightResolvent (c.value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))=
  OriginalKCommonGapKernelSource.actualCommonFKMeanPrice observation nontrivial half h at FKprice
 have old:=OriginalKFourierSectorRGramSource.actual_sector_complete_M_prices observation nontrivial half h
 have current:=OriginalKSectorEulerMixedSource.actual_coupled_complete_M_prices observation nontrivial half h
 rw [old.1,current.1] at Kprice
 rw [old.2,current.2] at FKprice
 have Kfield:=actual_complete_weighted_M_field_price c h (K c)
 have FKfield:=actual_complete_weighted_M_field_price c h (Fphysical (K c))
 rw [mul_assoc,Kprice] at Kfield
 rw [mul_assoc,FKprice] at FKfield
 exact ⟨Kfield,FKfield⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCoupledPhysicalRFieldSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
