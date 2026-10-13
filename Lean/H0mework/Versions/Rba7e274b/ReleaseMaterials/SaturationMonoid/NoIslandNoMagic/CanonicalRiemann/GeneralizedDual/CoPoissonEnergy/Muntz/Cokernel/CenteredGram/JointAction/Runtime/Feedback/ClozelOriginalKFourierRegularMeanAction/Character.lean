import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierRegularMeanAction.Price
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierRegularMeanAction
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

/-- Original character directly consumes the generated weighted regular response with complete remaining inventory. -/
theorem actual_Fourier_regular_priced_character_source (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 let weight:=b*star b
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let fkprice:=inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2))
 weight*(A*OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h)=
 weight*(characterPrice*star a*star
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h+
    OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h)-
 star characterPrice*a*
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h-
    OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h))-
 characterPrice*(weight*((2*star a)*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)-
   A*OriginalKInsideDebtRSource.actualWavePaPairPrice observation nontrivial half h nonnegative bounded-
   A*star a*(OriginalKPositionQuarterFTCAction.actualPositionQuarterPairPrice observation nontrivial half h+
     OriginalKFourierQuarterRplusAction.actualFourierQuarterPairPrice observation nontrivial half h+
     star (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h)*
       OriginalKQuarterTailPhysicalSource.actualQuarterTailPairPrice observation nontrivial half))-
   A*star a*b*star (actualWeightedKMeanRPrice observation nontrivial half h+b*fkprice))+
 star characterPrice*(weight*((2*a)*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
   A*OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded+
   A*a*(OriginalKPositionQuarterFTCAction.actualPositionQuarterSiblingPrice observation nontrivial half h+
     OriginalKFourierQuarterRplusAction.actualFourierQuarterSiblingPrice observation nontrivial half h+
     OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*
       OriginalKQuarterTailPhysicalSource.actualQuarterTailSiblingPrice observation nontrivial half))+
   A*a*star b*(actualWeightedKMeanRPrice observation nontrivial half h-b*fkprice)) := by
 have source:=OriginalKLiteralEdgeMeanSourcePrice.actual_literal_edge_priced_character_source observation nontrivial half h nonnegative bounded
 have prices:=actual_weighted_mean_price_faces observation nontrivial half h
 dsimp only at source prices ⊢
 have weighted:=congrArg (fun price : ℂ =>
   (star (OriginalRieszSource.Kernel.beta (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))*
     star (star (OriginalRieszSource.Kernel.beta (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))))*price) source
 linear_combination weighted+
   (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
     (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h))*
     OriginalKSourceScaledMaximalResponse.Return.sourceA observation*
     star (OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*prices.1+
   star (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
     (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h))*
     OriginalKSourceScaledMaximalResponse.Return.sourceA observation*
     OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*prices.2

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierRegularMeanAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
