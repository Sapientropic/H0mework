import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRealCoordinateSourceUnit.Primitive
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRealCoordinateSourceUnit
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local instance unweightedCharacterComplete : CompleteSpace BurnolPaAmbientCarrier :=by
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



def actualUnweightedCharacterRead (h:ℝ) (_nonnegative:0≤h) (_bounded:h≤Real.log 2) (kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice:ℂ):ℂ:=
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 characterPrice*star a*star
   (kforcingPrice+
    forcingPrice)-
 star characterPrice*a*
   (kforcingPrice-
    forcingPrice)-
 characterPrice*((2*star a)*pairPrice-
   A*wavePairPrice-
   A*star a*((OriginalKCharacterActionSource.actualPositionSourcePairPrice observation nontrivial half h+OriginalKCharacterActionSource.actualFourierSourcePairPrice observation nontrivial half h+star (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h)*OriginalKCharacterActionSource.actualTailSourcePairPrice observation nontrivial half)+star (kprice+fprice)))+
 star characterPrice*((2*a)*siblingPrice+
   A*waveSiblingPrice+
   A*a*((OriginalKCharacterActionSource.actualPositionSourceSiblingPrice observation nontrivial half h+OriginalKCharacterActionSource.actualFourierSourceSiblingPrice observation nontrivial half h+OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*OriginalKCharacterActionSource.actualTailSourceSiblingPrice observation nontrivial half)+(kprice-fprice)))



/-- The complete original character exposes its natural existing star-kappa/kappa effect; no unit or target value is supplied. -/
theorem actual_complete_character_kappa_factor (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2)
 (kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice:ℂ):
 OriginalKCharacterActionSource.actualDeterminantFreeCharacterRead observation nontrivial half h nonnegative bounded
  (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*kprice)
  (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*fprice)
  forcingPrice kforcingPrice
  (star (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)*pairPrice)
  (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*siblingPrice)
  wavePairPrice waveSiblingPrice=
 (star (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)*OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)*
 actualUnweightedCharacterRead observation nontrivial half h nonnegative bounded
  kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice :=by
 unfold OriginalKCharacterActionSource.actualDeterminantFreeCharacterRead actualUnweightedCharacterRead
 dsimp only
 simp only [star_add,star_mul]
 ring

def actualUnweightedFiniteCharacter (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 (OriginalKSourceScaledMaximalResponse.Return.sourceA observation)⁻¹*
 actualUnweightedCharacterRead observation nontrivial half h nonnegative bounded
 (actualUnweightedFiniteKPrice c h n) (actualUnweightedFiniteFKPrice c h n)
 (OriginalKFourierForcingCofinalAction.actualFiniteFourierForcingPrice c h n)
 (OriginalKPrimitivePhysicalSourceAction.actualFiniteKForcingPrice observation nontrivial half h n)
 (actualUnweightedPrimitivePairPrice observation nontrivial half h n)
 (actualUnweightedPrimitiveSiblingPrice observation nontrivial half h n)
 (OriginalKPaCountingSourceAction.actualFiniteWavePairPrice observation nontrivial half h nonnegative bounded n)
 (OriginalKPaCountingSourceAction.actualFiniteWaveSiblingPrice observation nontrivial half h nonnegative bounded n)

def actualOriginalCharacterSourceWeight:ℂ:=
 (star (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)*OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)*
 OriginalKSourceScaledMaximalResponse.Return.sourceA observation

/-- The source weight's units are paid by the same real-coordinate Abel source and original physical response factor. -/
theorem actual_original_character_source_weight_ne_zero:actualOriginalCharacterSourceWeight observation nontrivial half≠0:=by
 unfold actualOriginalCharacterSourceWeight
 exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr (actual_original_response_kappa_ne_zero observation nontrivial half))
  (actual_original_response_kappa_ne_zero observation nontrivial half)) (actual_original_return_sourceA_ne_zero observation nontrivial half)

/-- Current whole character BODY consumes the actual unweighted M and both primitive feet before removing its source units. -/
theorem actual_current_unweighted_character_factor (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 OriginalKCharacterActionSource.actualDeterminantFreeFiniteCharacter observation nontrivial half h nonnegative bounded n=
 actualOriginalCharacterSourceWeight observation nontrivial half*actualUnweightedFiniteCharacter observation nontrivial half h nonnegative bounded n :=by
 have M:=actual_original_M_kappa_price_factors observation nontrivial half h n
 have primitive:=actual_original_primitive_kappa_price_factors observation nontrivial half h n
 unfold OriginalKCharacterActionSource.actualDeterminantFreeFiniteCharacter
 rw [M.1,M.2,primitive.1,primitive.2,actual_complete_character_kappa_factor]
 unfold actualOriginalCharacterSourceWeight actualUnweightedFiniteCharacter
 have unit:=actual_original_return_sourceA_ne_zero observation nontrivial half
 simp only [mul_assoc,←mul_assoc (OriginalKSourceScaledMaximalResponse.Return.sourceA observation),mul_inv_cancel₀ unit,one_mul]

def actualUnweightedCharacterResidual (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 (actualOriginalCharacterSourceWeight observation nontrivial half)⁻¹*
 OriginalKCharacterActionSource.actualDeterminantFreeCharacterResidual observation nontrivial half h nonnegative bounded n

/-- The independent original kernel cross consumes the generated source units and complete literal current BODY; every original source residue remains faithful. -/
theorem actual_original_unweighted_character (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h=
 actualUnweightedFiniteCharacter observation nontrivial half h nonnegative bounded n+
 actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n :=by
 let W:=actualOriginalCharacterSourceWeight observation nontrivial half
 have unit:W≠0:=actual_original_character_source_weight_ne_zero observation nontrivial half
 have source:=OriginalKCharacterActionSource.actual_original_determinant_free_character observation nontrivial half h nonnegative bounded n
 rw [actual_current_unweighted_character_factor] at source
 have target:OriginalKCharacterActionSource.actualDeterminantFreeOriginalCharacter observation nontrivial half h=
  W*OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h:=by
  unfold OriginalKCharacterActionSource.actualDeterminantFreeOriginalCharacter
  dsimp only [W,actualOriginalCharacterSourceWeight]
  ring
 rw [target] at source
 change W*OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h=
  W*actualUnweightedFiniteCharacter observation nontrivial half h nonnegative bounded n+_ at source
 have generated:=congrArg (fun value:ℂ=>W⁻¹*value) source
 simp only [mul_add,←mul_assoc,inv_mul_cancel₀ unit,one_mul] at generated
 exact generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRealCoordinateSourceUnit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
