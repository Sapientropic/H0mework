import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCountingSourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCharacterActionSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local instance quarterConsumerComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "K" => burnolCompletedMellinRieszVector
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "H" => OriginalKCommonGapKernelSource.actualCommonField
local notation "velocity" => OriginalKCommonGapKernelSource.actualCommonVelocity

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)


def actualPositionSourcePairPrice (h:ℝ):ℂ:=
 (1/2:ℂ)*(star (OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c)+
  star (OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c))*
 star (OriginalKPositionQuarterFTCAction.actualPositionQuarterMean observation nontrivial half h)
def actualPositionSourceSiblingPrice (h:ℝ):ℂ:=
 (1/2:ℂ)*(OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c-
  OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c)*
 OriginalKPositionQuarterFTCAction.actualPositionQuarterMean observation nontrivial half h
def actualFourierSourcePairPrice (h:ℝ):ℂ:=
 (1/2:ℂ)*(star (OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c)+
  star (OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c))*
 star (OriginalKFourierQuarterRplusAction.actualFourierQuarterMean observation nontrivial half h)
def actualFourierSourceSiblingPrice (h:ℝ):ℂ:=
 (1/2:ℂ)*(OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c-
  OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c)*
 OriginalKFourierQuarterRplusAction.actualFourierQuarterMean observation nontrivial half h
def actualTailSourcePairPrice:ℂ:=
 -(2:ℂ)*star (OriginalKStaticKernelSourceGramSource.actualDualKernelGram c+
  OriginalKStaticKernelSourceGramSource.actualFourierDualGram c)+
 (2*burnolMellinGapMoment (OriginalKQuarterTailPhysicalSource.actualStarSource c).value)*
 (star (OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c)+
  star (OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c))
def actualTailSourceSiblingPrice:ℂ:=
 -(2:ℂ)*(OriginalKStaticKernelSourceGramSource.actualDualKernelGram c-
  OriginalKStaticKernelSourceGramSource.actualFourierDualGram c)+
 (2*star (burnolMellinGapMoment (OriginalKQuarterTailPhysicalSource.actualStarSource c).value))*
 (OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c-
  OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c)

/-- The quarter fields consume the exact already-generated original means and source dual Gram. -/
theorem actual_paid_quarter_source_prices (h:ℝ):
 OriginalKPositionQuarterFTCAction.actualPositionQuarterPairPrice observation nontrivial half h=actualPositionSourcePairPrice observation nontrivial half h ∧
 OriginalKPositionQuarterFTCAction.actualPositionQuarterSiblingPrice observation nontrivial half h=actualPositionSourceSiblingPrice observation nontrivial half h ∧
 OriginalKFourierQuarterRplusAction.actualFourierQuarterPairPrice observation nontrivial half h=actualFourierSourcePairPrice observation nontrivial half h ∧
 OriginalKFourierQuarterRplusAction.actualFourierQuarterSiblingPrice observation nontrivial half h=actualFourierSourceSiblingPrice observation nontrivial half h ∧
 OriginalKQuarterTailPhysicalSource.actualQuarterTailPairPrice observation nontrivial half=actualTailSourcePairPrice observation nontrivial half ∧
 OriginalKQuarterTailPhysicalSource.actualQuarterTailSiblingPrice observation nontrivial half=actualTailSourceSiblingPrice observation nontrivial half :=by
 have means:=OriginalKGapKernelGreenSource.actual_original_two_gap_mean_prices c
 have km:FiniteMobiusResolventFlux.actualMean (K c:BurnolL2)=star (OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c):=by
  simpa only [star_star] using congrArg star means.1
 have fm:FiniteMobiusResolventFlux.actualMean (fourierL2 (K c:BurnolL2))=star (OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c):=by
  simpa only [star_star] using congrArg star means.2
 have Gram:=OriginalKStaticKernelSourceGramSource.actual_original_static_source_Gram_feet c
 have dual:inner ℂ (K c) (K (OriginalKQuarterTailPhysicalSource.actualStarSource c))=OriginalKStaticKernelSourceGramSource.actualDualKernelGram c:=Gram.2.1
 unfold OriginalKPositionQuarterFTCAction.actualPositionQuarterPairPrice
  OriginalKPositionQuarterFTCAction.actualPositionQuarterSiblingPrice
  OriginalKFourierQuarterRplusAction.actualFourierQuarterPairPrice
  OriginalKFourierQuarterRplusAction.actualFourierQuarterSiblingPrice
  OriginalKQuarterTailPhysicalSource.actualQuarterTailPairPrice
  OriginalKQuarterTailPhysicalSource.actualQuarterTailSiblingPrice
 dsimp only
 rw [km,fm,dual]
 simp only [star_star]
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def actualPaidQuarterCharacterRead (h:ℝ) (_nonnegative:0≤h) (_bounded:h≤Real.log 2) (kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice:ℂ):ℂ:=
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 let W:=star D*D
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 let T:=star κ*κ
 T*W*characterPrice*star a*star
   (kforcingPrice+
    forcingPrice)-
 T*W*star characterPrice*a*
   (kforcingPrice-
    forcingPrice)-
 characterPrice*(κ*W*(2*star a)*pairPrice-
   T*W*A*wavePairPrice-
   A*star a*(T*W*(actualPositionSourcePairPrice observation nontrivial half h+actualFourierSourcePairPrice observation nontrivial half h+star (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h)*actualTailSourcePairPrice observation nontrivial half)+κ*D*star (kprice+fprice)))+
 star characterPrice*(star κ*W*(2*a)*siblingPrice+
   T*W*A*waveSiblingPrice+
   A*a*(T*W*(actualPositionSourceSiblingPrice observation nontrivial half h+actualFourierSourceSiblingPrice observation nontrivial half h+OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*actualTailSourceSiblingPrice observation nontrivial half)+star κ*star D*(kprice-fprice)))

/-- Current complete character BODY consumes every paid quarter mean and source dual foot; no new source event or price premise is introduced. -/
theorem actual_current_paid_quarter_character_read (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2)
 (kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice:ℂ):
 OriginalKPaCountingSourceAction.actualPaCountingCharacterRead observation nontrivial half h nonnegative bounded
  kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice=
 actualPaidQuarterCharacterRead observation nontrivial half h nonnegative bounded
  kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice :=by
 have paid:=actual_paid_quarter_source_prices observation nontrivial half h
 unfold OriginalKPaCountingSourceAction.actualPaCountingCharacterRead
 rw [paid.1,paid.2.1,paid.2.2.1,paid.2.2.2.1,paid.2.2.2.2.1,paid.2.2.2.2.2]
 rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCharacterActionSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
