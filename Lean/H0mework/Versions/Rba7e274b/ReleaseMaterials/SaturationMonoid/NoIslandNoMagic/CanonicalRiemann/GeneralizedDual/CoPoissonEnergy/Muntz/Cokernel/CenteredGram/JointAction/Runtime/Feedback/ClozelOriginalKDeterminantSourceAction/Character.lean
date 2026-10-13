import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDeterminantSourceAction.MSource
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDeterminantSourceAction.Quarter
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
local instance determinantCharacterComplete : CompleteSpace BurnolPaAmbientCarrier :=by
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


def actualDeterminantFreeCharacterRead (h:ℝ) (_nonnegative:0≤h) (_bounded:h≤Real.log 2) (kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice:ℂ):ℂ:=
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 let T:=star κ*κ
 T*characterPrice*star a*star
   (kforcingPrice+
    forcingPrice)-
 T*star characterPrice*a*
   (kforcingPrice-
    forcingPrice)-
 characterPrice*(κ*(2*star a)*pairPrice-
   T*A*wavePairPrice-
   A*star a*(T*(actualPositionSourcePairPrice observation nontrivial half h+actualFourierSourcePairPrice observation nontrivial half h+star (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h)*actualTailSourcePairPrice observation nontrivial half)+κ*star (kprice+fprice)))+
 star characterPrice*(star κ*(2*a)*siblingPrice+
   T*A*waveSiblingPrice+
   A*a*(T*(actualPositionSourceSiblingPrice observation nontrivial half h+actualFourierSourceSiblingPrice observation nontrivial half h+OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*actualTailSourceSiblingPrice observation nontrivial half)+star κ*(kprice-fprice)))


def actualDeterminantFreeFiniteCharacter (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 actualDeterminantFreeCharacterRead observation nontrivial half h nonnegative bounded
 (actualDeterminantFreeFiniteKPrice c h n)
 (actualDeterminantFreeFiniteFKPrice c h n)
 (OriginalKFourierForcingCofinalAction.actualFiniteFourierForcingPrice c h n)
 (OriginalKPrimitivePhysicalSourceAction.actualFiniteKForcingPrice observation nontrivial half h n)
 (OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitivePairPrice observation nontrivial half h n)
 (OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitiveSiblingPrice observation nontrivial half h n)
 (OriginalKPaCountingSourceAction.actualFiniteWavePairPrice observation nontrivial half h nonnegative bounded n)
 (OriginalKPaCountingSourceAction.actualFiniteWaveSiblingPrice observation nontrivial half h nonnegative bounded n)

/-- Exact scalar effect of the literal complete character BODY; no factor is assumed to be a unit here. -/
theorem actual_complete_character_determinant_factor (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2)
 (kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice:ℂ):
 actualPaidQuarterCharacterRead observation nontrivial half h nonnegative bounded
  (OriginalKCommonGapKernelSource.actualCommonDeterminant c*kprice)
  (OriginalKCommonGapKernelSource.actualCommonDeterminant c*fprice)
  forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice=
 (star (OriginalKCommonGapKernelSource.actualCommonDeterminant c)*OriginalKCommonGapKernelSource.actualCommonDeterminant c)*
 actualDeterminantFreeCharacterRead observation nontrivial half h nonnegative bounded
  kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice :=by
 unfold actualPaidQuarterCharacterRead actualDeterminantFreeCharacterRead
 dsimp only
 simp only [star_add,star_mul]
 ring

/-- The current literal finite character consumes the complete source price factorization and every paid quarter field. -/
theorem actual_current_finite_character_determinant_factor (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 OriginalKPaCountingSourceAction.actualFinitePaCountingCharacter observation nontrivial half h nonnegative bounded n=
 (star (OriginalKCommonGapKernelSource.actualCommonDeterminant c)*OriginalKCommonGapKernelSource.actualCommonDeterminant c)*
 actualDeterminantFreeFiniteCharacter observation nontrivial half h nonnegative bounded n :=by
 have prices:=actual_original_M_determinant_price_factors observation nontrivial half h n
 unfold OriginalKPaCountingSourceAction.actualFinitePaCountingCharacter
 rw [actual_current_paid_quarter_character_read,prices.1,prices.2.1]
 exact actual_complete_character_determinant_factor observation nontrivial half h nonnegative bounded _ _ _ _ _ _ _ _

def actualDeterminantFreeOriginalCharacter (h:ℝ):ℂ:=
 (star (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)*OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)*
 (OriginalKSourceScaledMaximalResponse.Return.sourceA observation*
  OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h)

def actualDeterminantFreeCharacterResidual (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 (star (OriginalKCommonGapKernelSource.actualCommonDeterminant c)*OriginalKCommonGapKernelSource.actualCommonDeterminant c)⁻¹*
 (OriginalKPaCountingSourceAction.actualPaCountingCharacterResidual observation nontrivial half h nonnegative bounded n+
  OriginalKPrimitivePhysicalSourceAction.actualPrimitiveCharacterResidual observation nontrivial half h n+
  OriginalKFourierForcingCofinalAction.actualForcingCharacterResidual observation nontrivial half h n+
  OriginalKFullKernelCofinalSource.actualFourierDualCharacterResidual observation nontrivial half h n+
  OriginalKCompleteMCofinalSource.actualCharacterSourceResidual observation nontrivial half h n)

/-- The independent original character removes the generated determinant branch, retaining all five faithful source residues and kappa. -/
theorem actual_original_determinant_free_character (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 actualDeterminantFreeOriginalCharacter observation nontrivial half h=
 actualDeterminantFreeFiniteCharacter observation nontrivial half h nonnegative bounded n+
 actualDeterminantFreeCharacterResidual observation nontrivial half h nonnegative bounded n :=by
 let W:=star (OriginalKCommonGapKernelSource.actualCommonDeterminant c)*OriginalKCommonGapKernelSource.actualCommonDeterminant c
 have unit:W≠0:=mul_ne_zero (star_ne_zero.mpr (actual_original_common_determinant_ne_zero observation nontrivial half))
  (actual_original_common_determinant_ne_zero observation nontrivial half)
 have source:=OriginalKPaCountingSourceAction.actual_original_finite_Pa_counting_character observation nontrivial half h nonnegative bounded n
 have actual:=actual_current_finite_character_determinant_factor observation nontrivial half h nonnegative bounded n
 rw [actual] at source
 have target:OriginalKFullKernelCofinalSource.actualOriginalCharacterValue observation nontrivial half h=
  W*actualDeterminantFreeOriginalCharacter observation nontrivial half h:=by
  unfold OriginalKFullKernelCofinalSource.actualOriginalCharacterValue actualDeterminantFreeOriginalCharacter
  dsimp only
  dsimp only [W]
  ring
 rw [target] at source
 have regroup:W*actualDeterminantFreeOriginalCharacter observation nontrivial half h=
  W*actualDeterminantFreeFiniteCharacter observation nontrivial half h nonnegative bounded n+
  (OriginalKPaCountingSourceAction.actualPaCountingCharacterResidual observation nontrivial half h nonnegative bounded n+
   OriginalKPrimitivePhysicalSourceAction.actualPrimitiveCharacterResidual observation nontrivial half h n+
   OriginalKFourierForcingCofinalAction.actualForcingCharacterResidual observation nontrivial half h n+
   OriginalKFullKernelCofinalSource.actualFourierDualCharacterResidual observation nontrivial half h n+
   OriginalKCompleteMCofinalSource.actualCharacterSourceResidual observation nontrivial half h n):=by
  linear_combination source
 have writeback:=congrArg (fun value:ℂ=>W⁻¹*value) regroup
 unfold actualDeterminantFreeCharacterResidual
 change actualDeterminantFreeOriginalCharacter observation nontrivial half h=
  actualDeterminantFreeFiniteCharacter observation nontrivial half h nonnegative bounded n+W⁻¹*_
 simp only [mul_add,←mul_assoc,inv_mul_cancel₀ unit,one_mul] at writeback
 linear_combination writeback

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCharacterActionSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
