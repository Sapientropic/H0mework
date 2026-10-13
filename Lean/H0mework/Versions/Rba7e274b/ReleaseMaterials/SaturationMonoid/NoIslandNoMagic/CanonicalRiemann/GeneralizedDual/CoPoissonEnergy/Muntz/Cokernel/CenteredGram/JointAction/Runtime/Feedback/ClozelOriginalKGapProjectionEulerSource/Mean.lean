import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapProjectionEulerSource.Kernel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
open Complex MeasureTheory Set Filter FourierTransform SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

local instance gapMeanPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualMeanRSourcePrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
 (left : BurnolPaAmbientCarrier) : ℂ:=
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let Fleft:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius left
 (∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed coordinate h x)*
  star (actualFourierGapRPrice dual Fleft)+
 (∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed coordinate h x)*
  star (actualGapRPrice dual Fleft)

/-- The literal complete two-mean material consumes the actual two source responses before any target character price. -/
theorem actual_full_mean_R_source_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
 (left : BurnolPaAmbientCarrier) :
 inner ℂ (left:BurnolL2) (burnolDirectRightResolvent (coordinate.value/2)
  (OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h:BurnolL2))=
 actualMeanRSourcePrice coordinate h left :=by
 have source:=actual_physical_gap_R_prices coordinate left
 unfold OriginalKGapMeanRSourceAction.Full.meanDebt OriginalRieszFiniteSynthesis.gapMeanAdjoint
 simp only [ContinuousLinearMap.toSpanSingleton_apply,map_smul]
 change inner ℂ (left:BurnolL2)
  (burnolDirectRightResolventCLM coordinate
   (((∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed coordinate h x):ℂ) •
    (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2)+
    ((∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed coordinate h x):ℂ) •
    fourierL2 (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2)))=_
 rw [map_add,map_smul,map_smul,inner_add_right,inner_smul_right,inner_smul_right]
 change (∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed coordinate h x)*
  inner ℂ (left:BurnolL2) (burnolDirectRightResolvent (coordinate.value/2) (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2))+
  (∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed coordinate h x)*
  inner ℂ (left:BurnolL2) (burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2)))=_
 rw [source.1,source.2]
 rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualGapSourceKMeanPrice (h : ℝ) : ℂ:=
 actualMeanRSourcePrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h
  (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))
def actualGapSourceFKMeanPrice (h : ℝ) : ℂ:=
 actualMeanRSourcePrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)))

/-- Original K and F K retain their own physical faces while reading the same original complete M. -/
theorem actual_original_K_FK_mean_source_price (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 inner ℂ (burnolCompletedMellinRieszVector coordinate:BurnolL2)
  (OriginalKFullSourceRResponse.Op.R observation nontrivial half (material:BurnolL2))=
 actualGapSourceKMeanPrice observation nontrivial half h ∧
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate:BurnolL2))
  (OriginalKFullSourceRResponse.Op.R observation nontrivial half (material:BurnolL2))=
 actualGapSourceFKMeanPrice observation nontrivial half h :=by
 dsimp only
 rw [OriginalKCombCofinalRAction.original_R_direct]
 constructor
 · exact actual_full_mean_R_source_price
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h
    (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))
 · exact actual_full_mean_R_source_price
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h
    (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
     (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
