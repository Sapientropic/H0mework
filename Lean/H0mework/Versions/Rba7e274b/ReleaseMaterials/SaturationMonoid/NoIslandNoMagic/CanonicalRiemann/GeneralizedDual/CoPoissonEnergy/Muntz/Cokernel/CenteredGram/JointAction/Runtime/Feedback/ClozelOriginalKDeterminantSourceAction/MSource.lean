import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDeterminantSourceAction.Source
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
local instance determinantMComplete : CompleteSpace BurnolPaAmbientCarrier :=by
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


/-- Actual original R acts before its physical dependent face; the generated source unit removes D while kappa remains. -/
theorem actual_original_M_determinant_free_action (h:ℝ):
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c •
 burnolEvenAmbientProjection (burnolDirectRightResolvent ((c).value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))=
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c •
 OriginalKCompleteMResidualSource.actualCompleteMSourceInventoryField c h :=by
 have generated:=OriginalKCompleteMResidualSource.actual_original_complete_M_inventory_action c h
 have source:=actual_original_common_determinant_ne_zero observation nontrivial half
 have acted:=congrArg (fun value:BurnolPaAmbientCarrier=>
  (OriginalKCommonGapKernelSource.actualCommonDeterminant c)⁻¹ • value) generated
 have coefficient:(OriginalKCommonGapKernelSource.actualCommonDeterminant c)⁻¹*
  (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c)=
  OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c:=by
  rw [mul_comm (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c),←mul_assoc,inv_mul_cancel₀ source,one_mul]
 simpa only [smul_smul,coefficient] using acted

/-- The complete finite source and its faithful residue are written back to the same R occurrence without a determinant gate. -/
theorem actual_original_M_determinant_free_finite_action (h:ℝ) (n:Nat):
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c •
 burnolEvenAmbientProjection (burnolDirectRightResolvent ((c).value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))=
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c •
 (OriginalKCompleteMCofinalSource.actualFiniteMInventoryField c h n+
  OriginalKCompleteMCofinalSource.actualMSourceTateResidual c h n •
  OriginalKCompleteMResidualSource.actualMeanZeroCompactRField c) :=by
 have generated:=OriginalKCompleteMCofinalSource.actual_original_M_finite_source_action c h n
 have source:=actual_original_common_determinant_ne_zero observation nontrivial half
 have acted:=congrArg (fun value:BurnolPaAmbientCarrier=>
  (OriginalKCommonGapKernelSource.actualCommonDeterminant c)⁻¹ • value) generated
 have coefficient:(OriginalKCommonGapKernelSource.actualCommonDeterminant c)⁻¹*
  (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c)=
  OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c:=by
  rw [mul_comm (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c),←mul_assoc,inv_mul_cancel₀ source,one_mul]
 simpa only [smul_smul,coefficient] using acted

def actualDeterminantFreeFiniteKPrice (coordinate:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℂ:=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa coordinate)*(OriginalKCompleteMCofinalSource.actualFiniteMSourceTateInventory coordinate h n*OriginalKCompleteMCofinalSource.actualMSourceKResponsePrice coordinate-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)*
 OriginalKCompleteMResidualSource.actualMSourceVCoefficient coordinate h)*OriginalKStaticKernelSourceGramSource.actualDualKernelGram coordinate-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass coordinate h)*(OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice coordinate)-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass coordinate h)*(OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice coordinate))
def actualDeterminantFreeFiniteFKPrice (coordinate:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℂ:=
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa coordinate*(OriginalKCompleteMCofinalSource.actualFiniteMSourceTateInventory coordinate h n*
  (-2*OriginalKFullKernelCofinalSource.actualFiniteFourierDual coordinate n+OriginalKCompleteMResidualSource.actualMeanZeroGapCoefficient coordinate*
   OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice coordinate)-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)*
  OriginalKCompleteMResidualSource.actualMSourceVCoefficient coordinate h)*OriginalKFullKernelCofinalSource.actualFiniteFourierDual coordinate n-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass coordinate h)*OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice coordinate-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass coordinate h)*OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice coordinate)
def actualDeterminantFreeSourceKPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa coordinate)*
 (OriginalKCompleteMResidualSource.actualMSourceTateInventory coordinate h*(-2*OriginalKStaticKernelSourceGramSource.actualDualKernelGram coordinate+
  OriginalKCompleteMResidualSource.actualMeanZeroGapCoefficient coordinate*OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice coordinate)-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)*
  OriginalKCompleteMResidualSource.actualMSourceVCoefficient coordinate h)*OriginalKStaticKernelSourceGramSource.actualDualKernelGram coordinate-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass coordinate h)*OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice coordinate-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass coordinate h)*OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice coordinate)

def actualDeterminantFreeSourceFKPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa coordinate)*
 (OriginalKCompleteMResidualSource.actualMSourceTateInventory coordinate h*(-2*OriginalKStaticKernelSourceGramSource.actualFourierDualGram coordinate+
  OriginalKCompleteMResidualSource.actualMeanZeroGapCoefficient coordinate*OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice coordinate)-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)*
  OriginalKCompleteMResidualSource.actualMSourceVCoefficient coordinate h)*OriginalKStaticKernelSourceGramSource.actualFourierDualGram coordinate-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass coordinate h)*OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice coordinate-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass coordinate h)*OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice coordinate)

/-- Literal actual source and finite fields retain every price leg; no inverse determinant is a constructor input. -/
theorem actual_original_M_determinant_price_factors (h:ℝ) (n:Nat):
 OriginalKCompleteMCofinalSource.actualFiniteKMeanDebtPrice c h n=
 OriginalKCommonGapKernelSource.actualCommonDeterminant c*actualDeterminantFreeFiniteKPrice c h n ∧
 OriginalKFullKernelCofinalSource.actualDoubleFiniteFKMeanDebtPrice c h n=
 OriginalKCommonGapKernelSource.actualCommonDeterminant c*actualDeterminantFreeFiniteFKPrice c h n ∧
 OriginalKGapKernelGreenSource.actualGreenKMeanDebtPrice c h=
 OriginalKCommonGapKernelSource.actualCommonDeterminant c*actualDeterminantFreeSourceKPrice c h ∧
 OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice c h=
 OriginalKCommonGapKernelSource.actualCommonDeterminant c*actualDeterminantFreeSourceFKPrice c h :=by
 unfold OriginalKCompleteMCofinalSource.actualFiniteKMeanDebtPrice
  OriginalKCompleteMCofinalSource.actualMSourceWeight actualDeterminantFreeFiniteKPrice
  OriginalKFullKernelCofinalSource.actualDoubleFiniteFKMeanDebtPrice actualDeterminantFreeFiniteFKPrice
  OriginalKGapKernelGreenSource.actualGreenKMeanDebtPrice actualDeterminantFreeSourceKPrice
  OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice actualDeterminantFreeSourceFKPrice
 unfold OriginalKCompleteMCofinalSource.actualMSourceWeight
 constructor
 · ring
 constructor
 · ring
 constructor <;> ring

/-- Independent own physical readers consume the actual whole field after the source determinant unit has been generated. -/
theorem actual_original_M_determinant_free_own_prices (h:ℝ):
 inner ℂ (K c) (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c •
 burnolEvenAmbientProjection (burnolDirectRightResolvent ((c).value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2)))=
 actualDeterminantFreeSourceKPrice c h ∧
 inner ℂ (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (K c))
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c •
 burnolEvenAmbientProjection (burnolDirectRightResolvent ((c).value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2)))=
 actualDeterminantFreeSourceFKPrice c h :=by
 rw [actual_original_M_determinant_free_action]
 have source:=OriginalKGapKernelGreenSource.actual_original_two_gap_mean_prices c
 have fields:=OriginalKStaticKernelSourceGramSource.actual_static_G_FG_input_prices c
 have Gram:=OriginalKStaticKernelSourceGramSource.actual_original_static_source_Gram_feet c
 have dual:inner ℂ (K c) (K (OriginalKQuarterTailPhysicalSource.actualStarSource c))=OriginalKStaticKernelSourceGramSource.actualDualKernelGram c:=Gram.2.1
 unfold OriginalKCompleteMResidualSource.actualCompleteMSourceInventoryField
  OriginalKCompleteMResidualSource.actualMeanZeroCompactRField
 simp only [inner_smul_right,inner_add_right,inner_sub_right]
 rw [dual,fields.1,fields.2.1,fields.2.2.1,fields.2.2.2,source.1,source.2]
 exact ⟨rfl,rfl⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCharacterActionSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
