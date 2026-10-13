import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRealCoordinateSourceUnit.Units
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDeterminantSourceAction.Consumer
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
local instance unweightedMComplete : CompleteSpace BurnolPaAmbientCarrier :=by
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



/-- Generated original kappa is consumed only after actual R and its dependent physical face. -/
theorem actual_original_unweighted_M_source_action (h:ℝ):
 burnolEvenAmbientProjection (burnolDirectRightResolvent ((c).value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))=
 OriginalKCompleteMResidualSource.actualCompleteMSourceInventoryField c h :=by
 have original:=OriginalKCharacterActionSource.actual_original_M_determinant_free_action observation nontrivial half h
 have source:=actual_original_response_kappa_ne_zero observation nontrivial half
 have acted:=congrArg (fun field:BurnolPaAmbientCarrier=>
  (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)⁻¹ • field) original
 simpa only [smul_smul,inv_mul_cancel₀ source,one_smul] using acted

/-- Complete original material and faithful source residue have no remaining determinant/kappa gate. -/
theorem actual_original_unweighted_M_finite_action (h:ℝ) (n:Nat):
 burnolEvenAmbientProjection (burnolDirectRightResolvent ((c).value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))=
 OriginalKCompleteMCofinalSource.actualFiniteMInventoryField c h n+
 OriginalKCompleteMCofinalSource.actualMSourceTateResidual c h n • OriginalKCompleteMResidualSource.actualMeanZeroCompactRField c :=by
 have original:=OriginalKCharacterActionSource.actual_original_M_determinant_free_finite_action observation nontrivial half h n
 have source:=actual_original_response_kappa_ne_zero observation nontrivial half
 have acted:=congrArg (fun field:BurnolPaAmbientCarrier=>
  (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)⁻¹ • field) original
 simpa only [smul_smul,inv_mul_cancel₀ source,one_smul] using acted

/-- Original own K response is restored from its already-generated complete native field. -/
theorem actual_original_unweighted_R_kernel_field:
 burnolEvenAmbientProjection (burnolDirectRightResolvent ((c).value/2) (K c:BurnolL2))=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)⁻¹ •
 OriginalKSeedPhysicalRSource.actualSeedNativeWeightedKField c :=by
 have generated:=(OriginalKCoupledPhysicalRFieldSource.actual_original_weighted_R_fields c).1
 rw [(OriginalKSeedPhysicalRSource.actual_two_seed_native_weighted_fields c).1] at generated
 have source:=actual_original_response_kappa_ne_zero observation nontrivial half
 have acted:=congrArg (fun field:BurnolPaAmbientCarrier=>
  (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)⁻¹ • field) generated
 simpa only [smul_smul,inv_mul_cancel₀ source,one_smul] using acted

def actualUnweightedFiniteKPrice (coordinate:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℂ:=
 (OriginalKCompleteMCofinalSource.actualFiniteMSourceTateInventory coordinate h n*OriginalKCompleteMCofinalSource.actualMSourceKResponsePrice coordinate-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)*
 OriginalKCompleteMResidualSource.actualMSourceVCoefficient coordinate h)*OriginalKStaticKernelSourceGramSource.actualDualKernelGram coordinate-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass coordinate h)*(OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice coordinate)-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass coordinate h)*(OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice coordinate))
def actualUnweightedFiniteFKPrice (coordinate:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℂ:=
 (OriginalKCompleteMCofinalSource.actualFiniteMSourceTateInventory coordinate h n*
  (-2*OriginalKFullKernelCofinalSource.actualFiniteFourierDual coordinate n+OriginalKCompleteMResidualSource.actualMeanZeroGapCoefficient coordinate*
   OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice coordinate)-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)*
  OriginalKCompleteMResidualSource.actualMSourceVCoefficient coordinate h)*OriginalKFullKernelCofinalSource.actualFiniteFourierDual coordinate n-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass coordinate h)*OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice coordinate-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass coordinate h)*OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice coordinate)
def actualUnweightedSourceKPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 
 (OriginalKCompleteMResidualSource.actualMSourceTateInventory coordinate h*(-2*OriginalKStaticKernelSourceGramSource.actualDualKernelGram coordinate+
  OriginalKCompleteMResidualSource.actualMeanZeroGapCoefficient coordinate*OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice coordinate)-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)*
  OriginalKCompleteMResidualSource.actualMSourceVCoefficient coordinate h)*OriginalKStaticKernelSourceGramSource.actualDualKernelGram coordinate-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass coordinate h)*OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice coordinate-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass coordinate h)*OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice coordinate)

def actualUnweightedSourceFKPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 
 (OriginalKCompleteMResidualSource.actualMSourceTateInventory coordinate h*(-2*OriginalKStaticKernelSourceGramSource.actualFourierDualGram coordinate+
  OriginalKCompleteMResidualSource.actualMeanZeroGapCoefficient coordinate*OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice coordinate)-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)*
  OriginalKCompleteMResidualSource.actualMSourceVCoefficient coordinate h)*OriginalKStaticKernelSourceGramSource.actualFourierDualGram coordinate-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass coordinate h)*OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice coordinate-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass coordinate h)*OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice coordinate)


/-- Both independent physical readers consume the actual full unweighted field and all paid static feet. -/
theorem actual_original_unweighted_M_own_prices (h:ℝ):
 inner ℂ (K c) (burnolEvenAmbientProjection (burnolDirectRightResolvent ((c).value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2)))=actualUnweightedSourceKPrice c h ∧
 inner ℂ (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (K c))
 (burnolEvenAmbientProjection (burnolDirectRightResolvent ((c).value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2)))=actualUnweightedSourceFKPrice c h :=by
 rw [actual_original_unweighted_M_source_action]
 have source:=OriginalKGapKernelGreenSource.actual_original_two_gap_mean_prices c
 have fields:=OriginalKStaticKernelSourceGramSource.actual_static_G_FG_input_prices c
 have Gram:=OriginalKStaticKernelSourceGramSource.actual_original_static_source_Gram_feet c
 have dual:inner ℂ (K c) (K (OriginalKQuarterTailPhysicalSource.actualStarSource c))=OriginalKStaticKernelSourceGramSource.actualDualKernelGram c:=Gram.2.1
 unfold OriginalKCompleteMResidualSource.actualCompleteMSourceInventoryField
  OriginalKCompleteMResidualSource.actualMeanZeroCompactRField
 simp only [inner_add_right,inner_sub_right,inner_smul_right]
 rw [dual,fields.1,fields.2.1,fields.2.2.1,fields.2.2.2,source.1,source.2]
 exact ⟨rfl,rfl⟩

/-- Literal finite and source prices record their original kappa source factor before it is consumed. -/
theorem actual_original_M_kappa_price_factors (h:ℝ) (n:Nat):
 OriginalKCharacterActionSource.actualDeterminantFreeFiniteKPrice c h n=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*actualUnweightedFiniteKPrice c h n ∧
 OriginalKCharacterActionSource.actualDeterminantFreeFiniteFKPrice c h n=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*actualUnweightedFiniteFKPrice c h n :=by
 unfold OriginalKCharacterActionSource.actualDeterminantFreeFiniteKPrice actualUnweightedFiniteKPrice
  OriginalKCharacterActionSource.actualDeterminantFreeFiniteFKPrice actualUnweightedFiniteFKPrice
 exact ⟨rfl,rfl⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRealCoordinateSourceUnit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
