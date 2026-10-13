import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteMCofinalSource.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMCofinalSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance cofinalMPricePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


def actualMSourceWeight (c:BurnolCompletedMellinCoordinate):ℂ:=
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector

def actualMSourceKResponsePrice (c:BurnolCompletedMellinCoordinate):ℂ:=
 -2*OriginalKStaticKernelSourceGramSource.actualDualKernelGram c+
 OriginalKCompleteMResidualSource.actualMeanZeroGapCoefficient c*(OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c)

def actualMSourceFKResponsePrice (c:BurnolCompletedMellinCoordinate):ℂ:=
 -2*OriginalKStaticKernelSourceGramSource.actualFourierDualGram c+
 OriginalKCompleteMResidualSource.actualMeanZeroGapCoefficient c*(OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c)

def actualFiniteKMeanDebtPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℂ:=
 (actualMSourceWeight c)*(actualFiniteMSourceTateInventory c h n*actualMSourceKResponsePrice c-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*
 OriginalKCompleteMResidualSource.actualMSourceVCoefficient c h)*OriginalKStaticKernelSourceGramSource.actualDualKernelGram c-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass c h)*(OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c)-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass c h)*(OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c))

def actualFiniteFKMeanDebtPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℂ:=
 (actualMSourceWeight c)*(actualFiniteMSourceTateInventory c h n*actualMSourceFKResponsePrice c-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*
 OriginalKCompleteMResidualSource.actualMSourceVCoefficient c h)*OriginalKStaticKernelSourceGramSource.actualFourierDualGram c-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass c h)*(OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c)-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass c h)*(OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c))

/-- Both original physical feet read the finite complete M field produced by the actual source sequence. -/
theorem actual_finite_complete_M_own_prices (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):
 inner ℂ (K c) (actualMSourceWeight c • actualFiniteMInventoryField c h n)=actualFiniteKMeanDebtPrice c h n ∧
 inner ℂ (Fphysical (K c)) (actualMSourceWeight c • actualFiniteMInventoryField c h n)=actualFiniteFKMeanDebtPrice c h n :=by
 have Gram:=OriginalKStaticKernelSourceGramSource.actual_original_static_source_Gram_feet c
 have means:=OriginalKStaticKernelSourceGramSource.actual_static_G_FG_input_prices c
 have generated:=OriginalKGapKernelGreenSource.actual_original_two_gap_mean_prices c
 unfold actualFiniteMInventoryField OriginalKCompleteMResidualSource.actualMeanZeroCompactRField
 simp only [inner_smul_right,inner_add_right,inner_sub_right]
 have dual:inner ℂ (K c) (K (OriginalKQuarterTailPhysicalSource.actualStarSource c))=
  OriginalKStaticKernelSourceGramSource.actualDualKernelGram c:=Gram.2.1
 have Fdual:inner ℂ (Fphysical (K c)) (K (OriginalKQuarterTailPhysicalSource.actualStarSource c))=
  OriginalKStaticKernelSourceGramSource.actualFourierDualGram c:=rfl
 rw [dual,Fdual,means.1,means.2.1,means.2.2.1,means.2.2.2,generated.1,generated.2]
 exact ⟨rfl,rfl⟩

/-- Complete original M prices consume the actual same source residual rather than keeping an uncontrolled Tate input. -/
theorem actual_complete_M_finite_price_residuals (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):
 OriginalKGapKernelGreenSource.actualGreenKMeanDebtPrice c h-actualFiniteKMeanDebtPrice c h n=
 (actualMSourceWeight c)*actualMSourceTateResidual c h n*actualMSourceKResponsePrice c ∧
 OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice c h-actualFiniteFKMeanDebtPrice c h n=
 (actualMSourceWeight c)*actualMSourceTateResidual c h n*actualMSourceFKResponsePrice c :=by
 have source:=actual_complete_M_source_residual c h n
 have generated:OriginalKCompleteMResidualSource.actualMSourceTateInventory c h=
  actualFiniteMSourceTateInventory c h n+actualMSourceTateResidual c h n :=by linear_combination source
 unfold OriginalKGapKernelGreenSource.actualGreenKMeanDebtPrice OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice
 rw [generated]
 unfold actualFiniteKMeanDebtPrice actualFiniteFKMeanDebtPrice actualMSourceKResponsePrice actualMSourceFKResponsePrice actualMSourceWeight
 constructor <;> ring

/-- Each complete M price error is paid by the same actual source contraction and its own response factor. -/
theorem actual_complete_M_finite_price_error (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):
 ‖OriginalKGapKernelGreenSource.actualGreenKMeanDebtPrice c h-actualFiniteKMeanDebtPrice c h n‖≤
 ‖actualMSourceWeight c‖*‖actualMSourceKResponsePrice c‖*‖actualMSourceRead c h‖*
 ((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖)) ∧
 ‖OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice c h-actualFiniteFKMeanDebtPrice c h n‖≤
 ‖actualMSourceWeight c‖*‖actualMSourceFKResponsePrice c‖*‖actualMSourceRead c h‖*
 ((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖)) :=by
 have source:=actual_complete_M_finite_price_residuals c h n
 rw [source.1,source.2,norm_mul,norm_mul,norm_mul,norm_mul]
 constructor
 · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
   (actual_complete_M_source_error c h n) (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring)
 · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
   (actual_complete_M_source_error c h n) (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring)

/-- The original two complete M prices independently consume the existing actual source closure. -/
theorem actual_complete_M_finite_prices_tendsto (c:BurnolCompletedMellinCoordinate) (h:ℝ):
 Tendsto (actualFiniteKMeanDebtPrice c h) atTop (𝓝 (OriginalKGapKernelGreenSource.actualGreenKMeanDebtPrice c h)) ∧
 Tendsto (actualFiniteFKMeanDebtPrice c h) atTop (𝓝 (OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice c h)) :=by
 have source:=actual_complete_M_cofinal_source c h
 have constant (value:ℂ):Tendsto (fun _:Nat=>value) atTop (𝓝 value):=tendsto_const_nhds
 constructor
 · have generated:=((((source.mul_const (actualMSourceKResponsePrice c)).sub
    (constant ((2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization
     (OriginalKQuarterTailPhysicalSource.actualStarSource c)*OriginalKCompleteMResidualSource.actualMSourceVCoefficient c h)*
     OriginalKStaticKernelSourceGramSource.actualDualKernelGram c))).sub
    (constant ((2*OriginalKCompleteMResidualSource.actualPositionMSourceMass c h)*(OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c)))).sub
    (constant ((2*OriginalKCompleteMResidualSource.actualFourierMSourceMass c h)*(OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c)))).const_mul (actualMSourceWeight c)
   unfold actualFiniteKMeanDebtPrice
   simpa only [actualMSourceWeight,actualMSourceKResponsePrice,actualMSourceFKResponsePrice,OriginalKGapKernelGreenSource.actualGreenKMeanDebtPrice,OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice] using generated
 · have generated:=((((source.mul_const (actualMSourceFKResponsePrice c)).sub
    (constant ((2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization
     (OriginalKQuarterTailPhysicalSource.actualStarSource c)*OriginalKCompleteMResidualSource.actualMSourceVCoefficient c h)*
     OriginalKStaticKernelSourceGramSource.actualFourierDualGram c))).sub
    (constant ((2*OriginalKCompleteMResidualSource.actualPositionMSourceMass c h)*(OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c)))).sub
    (constant ((2*OriginalKCompleteMResidualSource.actualFourierMSourceMass c h)*(OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c)))).const_mul (actualMSourceWeight c)
   unfold actualFiniteFKMeanDebtPrice
   simpa only [actualMSourceWeight,actualMSourceKResponsePrice,actualMSourceFKResponsePrice,OriginalKGapKernelGreenSource.actualGreenKMeanDebtPrice,OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice] using generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMCofinalSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
