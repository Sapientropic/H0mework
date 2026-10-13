import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCommonGapKernelSource.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCommonGapKernelSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "K" => burnolCompletedMellinRieszVector
local notation "E" => OriginalRieszSource.GapEuler.euler
local notation "FT" => (fourierCLM ℂ (TemperedDistribution ℝ ℂ))
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The original paired and sibling character actually consume the same new complete source field, with the actual conjugate weight. -/
theorem actual_common_source_priced_character (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=actualCommonDeterminant (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 let W:=star D*D
 W*(A*OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h)=
 W*characterPrice*star a*star
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h+
    OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h)-
 W*star characterPrice*a*
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h-
    OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h)-
 characterPrice*(W*(2*star a)*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)-
   W*A*OriginalKInsideDebtRSource.actualWavePaPairPrice observation nontrivial half h nonnegative bounded-
   A*star a*(W*(OriginalKPositionQuarterFTCAction.actualPositionQuarterPairPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterPairPrice observation nontrivial half h+star (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h)*OriginalKQuarterTailPhysicalSource.actualQuarterTailPairPrice observation nontrivial half)+D*star (actualCommonKMeanPrice observation nontrivial half h+actualCommonFKMeanPrice observation nontrivial half h)))+
 star characterPrice*(W*(2*a)*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
   W*A*OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded+
   A*a*(W*(OriginalKPositionQuarterFTCAction.actualPositionQuarterSiblingPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterSiblingPrice observation nontrivial half h+OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*OriginalKQuarterTailPhysicalSource.actualQuarterTailSiblingPrice observation nontrivial half)+star D*(actualCommonKMeanPrice observation nontrivial half h-actualCommonFKMeanPrice observation nontrivial half h))) :=by
 let D:=actualCommonDeterminant (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 have prices:=actual_common_original_M_prices observation nontrivial half h
 change D*OriginalKGapProjectionEulerSource.actualGapSourceKMeanPrice observation nontrivial half h=actualCommonKMeanPrice observation nontrivial half h ∧
  D*OriginalKGapProjectionEulerSource.actualGapSourceFKMeanPrice observation nontrivial half h=actualCommonFKMeanPrice observation nontrivial half h at prices
 have paired:(star D*D)*star (OriginalKGapProjectionEulerSource.actualGapSourceKMeanPrice observation nontrivial half h+
  OriginalKGapProjectionEulerSource.actualGapSourceFKMeanPrice observation nontrivial half h)=
  D*star (actualCommonKMeanPrice observation nontrivial half h+actualCommonFKMeanPrice observation nontrivial half h) :=by
  rw [←prices.1,←prices.2]
  simp only [star_add,star_mul]
  ring
 have sibling:(star D*D)*(OriginalKGapProjectionEulerSource.actualGapSourceKMeanPrice observation nontrivial half h-
  OriginalKGapProjectionEulerSource.actualGapSourceFKMeanPrice observation nontrivial half h)=
  star D*(actualCommonKMeanPrice observation nontrivial half h-actualCommonFKMeanPrice observation nontrivial half h) :=by
  rw [←prices.1,←prices.2]
  ring
 have source:=OriginalKGapProjectionEulerSource.actual_gap_source_priced_character_source observation nontrivial half h nonnegative bounded
 dsimp only at source
 have weighted:=congrArg (fun price:ℂ=>(star D*D)*price) source
 dsimp only at weighted ⊢
 linear_combination weighted+characterPrice*A*star a*paired+star characterPrice*A*a*sibling

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCommonGapKernelSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
