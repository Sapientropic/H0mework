import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantSeedWholeRAction.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKConstantSeedWholeRAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)



local instance wholeSeedMeanPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualFSeedMeanRPrice (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 (-2/(coordinate.value-1):ℂ)*
 (star (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate)*
    inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
  (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2))

theorem actual_Fseed_mean_R_price (h : ℝ) :
 inner ℂ (fourierL2 ConstantSource.seed)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))=
 actualFSeedMeanRPrice observation nontrivial half h :=
 actual_Fconstant_seed_R_source_price _ _

def actualWholeSeedPricedKMeanRPrice (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let A:=star (OriginalRieszSource.Kernel.A coordinate)
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 (A*OriginalKCompactAdjointRSource.actualCompactFourierResponsePrice coordinate OriginalRieszSource.Response.wholeU material-
 b*OriginalKCompactAdjointRSource.actualCompactFourierResponsePrice coordinate OriginalRieszSource.Response.wholeV material-
 coordinate.value*A*((1/2:ℂ)*OriginalKGapMeanRSourceAction.actualMeanGram observation nontrivial half h/(coordinate.value/2))+
 (1-coordinate.value)*b*actualFSeedMeanRPrice observation nontrivial half h-
 (2:ℂ)*OriginalKConstantContactSourceAction.actualConstantContactMeanInputPrice observation nontrivial half h)/(2*coordinate.value-1)

/-- The actual whole seed source action is consumed in the unchanged original K price. -/
theorem actual_whole_seed_priced_K_mean (h : ℝ) :
 OriginalKCompactAdjointRSource.actualCompactPricedKMeanRPrice observation nontrivial half h=
 actualWholeSeedPricedKMeanRPrice observation nontrivial half h := by
 unfold OriginalKCompactAdjointRSource.actualCompactPricedKMeanRPrice actualWholeSeedPricedKMeanRPrice
 dsimp only
 rw [actual_Fseed_mean_R_price]


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKConstantSeedWholeRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
