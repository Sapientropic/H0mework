import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullKernelCofinalSource.Gram
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullKernelCofinalSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance kernelCofinalPricePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


namespace CurrentM
export OriginalKCompleteMCofinalSource
 (actualMSourceWeight actualFiniteMSourceTateInventory actualMSourceTateResidual actualMSourceRead
  actualMSourceKResponsePrice actualMSourceFKResponsePrice actualFiniteKMeanDebtPrice actualFiniteFKMeanDebtPrice
  actual_complete_M_finite_price_error actual_complete_M_finite_price_residuals
  actual_complete_M_finite_prices_tendsto actual_complete_M_cofinal_source)
end CurrentM

def actualDoubleFiniteFKMeanDebtPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℂ:=
 CurrentM.actualMSourceWeight c*(CurrentM.actualFiniteMSourceTateInventory c h n*
  (-2*actualFiniteFourierDual c n+OriginalKCompleteMResidualSource.actualMeanZeroGapCoefficient c*
   OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c)-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*
  OriginalKCompleteMResidualSource.actualMSourceVCoefficient c h)*actualFiniteFourierDual c n-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass c h)*OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass c h)*OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c)

def actualFiniteFourierDualPriceRead (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℂ:=
 -2*(CurrentM.actualFiniteMSourceTateInventory c h n+
  OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*
   OriginalKCompleteMResidualSource.actualMSourceVCoefficient c h)

/-- Current complete M's actual finite FK consumer reads the independently generated two whole-source FourierDual; its source discrepancy stays exact. -/
theorem actual_complete_M_Fourier_dual_finite_residual (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):
 CurrentM.actualFiniteFKMeanDebtPrice c h n-actualDoubleFiniteFKMeanDebtPrice c h n=
 CurrentM.actualMSourceWeight c*actualFiniteFourierDualPriceRead c h n*actualFourierDualSourceResidual c n :=by
 have source:=actual_original_Fourier_dual_source_residual c n
 have generated:OriginalKStaticKernelSourceGramSource.actualFourierDualGram c=
  actualFiniteFourierDual c n+actualFourierDualSourceResidual c n :=by linear_combination source
 unfold CurrentM.actualFiniteFKMeanDebtPrice CurrentM.actualMSourceFKResponsePrice
 rw [generated]
 unfold actualDoubleFiniteFKMeanDebtPrice actualFiniteFourierDualPriceRead
 ring

/-- The actual current finite M consumer pays its FourierDual discrepancy from the two original ambient source errors. -/
theorem actual_complete_M_Fourier_dual_finite_error (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):
 ‖CurrentM.actualFiniteFKMeanDebtPrice c h n-actualDoubleFiniteFKMeanDebtPrice c h n‖≤
 ‖CurrentM.actualMSourceWeight c‖*‖actualFiniteFourierDualPriceRead c h n‖*actualFourierDualSourceError c n :=by
 rw [actual_complete_M_Fourier_dual_finite_residual,norm_mul,norm_mul]
 have source:=actual_original_Fourier_dual_source_error c n
 rw [actual_original_Fourier_dual_source_residual] at source
 exact mul_le_mul_of_nonneg_left source (by positivity)

/-- The complete original M price has both actual source residues paid: eta/Tsquare currentM and the two original whole-K forcing fields. -/
theorem actual_original_M_double_finite_error (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):
 ‖OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice c h-actualDoubleFiniteFKMeanDebtPrice c h n‖≤
 ‖CurrentM.actualMSourceWeight c‖*‖CurrentM.actualMSourceFKResponsePrice c‖*‖CurrentM.actualMSourceRead c h‖*
 ((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖))+
 ‖CurrentM.actualMSourceWeight c‖*‖actualFiniteFourierDualPriceRead c h n‖*actualFourierDualSourceError c n :=by
 have split:OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice c h-actualDoubleFiniteFKMeanDebtPrice c h n=
  (OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice c h-CurrentM.actualFiniteFKMeanDebtPrice c h n)+
  (CurrentM.actualFiniteFKMeanDebtPrice c h n-actualDoubleFiniteFKMeanDebtPrice c h n) :=by ring
 rw [split]
 exact (norm_add_le _ _).trans (add_le_add (CurrentM.actual_complete_M_finite_price_error c h n).2
  (actual_complete_M_Fourier_dual_finite_error c h n))

/-- Both true source programmes feed the complete FK M price limit; no target Gram or terminal value is a finite producer input. -/
theorem actual_original_M_double_finite_tendsto (c:BurnolCompletedMellinCoordinate) (h:ℝ):
 Tendsto (actualDoubleFiniteFKMeanDebtPrice c h) atTop
  (𝓝 (OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice c h)) :=by
 have tate:=CurrentM.actual_complete_M_cofinal_source c h
 have dual:=actual_original_Fourier_dual_source_tendsto c
 have constant (value:ℂ):Tendsto (fun _:Nat=>value) atTop (𝓝 value):=tendsto_const_nhds
 have response:=(dual.const_mul (-2:ℂ)).add (constant (OriginalKCompleteMResidualSource.actualMeanZeroGapCoefficient c*
  OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c))
 have source:=((((tate.mul response).sub (dual.const_mul (2*
  OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*
  OriginalKCompleteMResidualSource.actualMSourceVCoefficient c h))).sub
  (constant ((2*OriginalKCompleteMResidualSource.actualPositionMSourceMass c h)*
   OriginalKGapKernelGreenSource.actualOriginalFKGapMeanPrice c))).sub
  (constant ((2*OriginalKCompleteMResidualSource.actualFourierMSourceMass c h)*
   OriginalKGapKernelGreenSource.actualOriginalKGapMeanPrice c))).const_mul (CurrentM.actualMSourceWeight c)
 unfold actualDoubleFiniteFKMeanDebtPrice
 simpa only [CurrentM.actualMSourceWeight,OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice,mul_comm] using source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullKernelCofinalSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
