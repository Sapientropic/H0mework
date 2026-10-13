import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapKernelGreenSource.FourierGram
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapKernelGreenSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance gapKernelPriceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "q" => (1/4:ℝ)
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "μ" => FiniteMobiusResolventFlux.actualMean

def actualOriginalKGapMeanPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
 ((1/2:ℂ)*(star (OriginalRieszSource.Kernel.A c)*Gap.actualGapA-
  star (OriginalRieszSource.Kernel.beta c)*Gap.actualGapBeta))/c.value
def actualOriginalFKGapMeanPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
 ((1/2:ℂ)*(star (OriginalRieszSource.Kernel.beta c)*Gap.actualGapA-
  star (OriginalRieszSource.Kernel.A c)*Gap.actualGapBeta))/(c.value-1)

/-- Both own physical mean feet read their already-generated original source Green equations; the source rates are paid afterwards. -/
theorem actual_original_two_gap_mean_prices (c : BurnolCompletedMellinCoordinate) :
 star (μ (K c:BurnolL2))=actualOriginalKGapMeanPrice c ∧
 star (μ (fourierL2 (K c:BurnolL2)))=actualOriginalFKGapMeanPrice c :=by
 have source:=actual_original_gap_kernel_Gram c
 have Fourier:=actual_original_Fourier_gap_kernel_Gram c
 have means:=OriginalKStaticKernelSourceGramSource.actual_static_G_FG_input_prices c
 have moved:=OriginalKGapProjectionEulerSource.actual_source_fourier_input (K c:BurnolL2) G
 change inner ℂ (Fphysical (K c)) G=inner ℂ (K c) (Fphysical G) at moved
 rw [←moved,means.2.1] at Fourier
 rw [means.1] at source
 have units:=OriginalKCommonGapKernelSource.actual_common_source_units c
 unfold actualOriginalKGapMeanPrice actualOriginalFKGapMeanPrice
 constructor
 · apply (eq_div_iff units.1).mpr
   linear_combination source
 · apply (eq_div_iff units.2).mpr
   linear_combination Fourier

def actualGreenKMeanDebtPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c)*
 (OriginalKCompleteMResidualSource.actualMSourceTateInventory c h*(-2*OriginalKStaticKernelSourceGramSource.actualDualKernelGram c+
  OriginalKCompleteMResidualSource.actualMeanZeroGapCoefficient c*actualOriginalKGapMeanPrice c)-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*
  OriginalKCompleteMResidualSource.actualMSourceVCoefficient c h)*OriginalKStaticKernelSourceGramSource.actualDualKernelGram c-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass c h)*actualOriginalKGapMeanPrice c-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass c h)*actualOriginalFKGapMeanPrice c)
def actualGreenFKMeanDebtPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c)*
 (OriginalKCompleteMResidualSource.actualMSourceTateInventory c h*(-2*OriginalKStaticKernelSourceGramSource.actualFourierDualGram c+
  OriginalKCompleteMResidualSource.actualMeanZeroGapCoefficient c*actualOriginalFKGapMeanPrice c)-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*
  OriginalKCompleteMResidualSource.actualMSourceVCoefficient c h)*OriginalKStaticKernelSourceGramSource.actualFourierDualGram c-
 (2*OriginalKCompleteMResidualSource.actualPositionMSourceMass c h)*actualOriginalFKGapMeanPrice c-
 (2*OriginalKCompleteMResidualSource.actualFourierMSourceMass c h)*actualOriginalKGapMeanPrice c)

/-- The complete same-source M consumes both generated original gap means; its Tate/FourierDual inventory remains explicit. -/
theorem actual_complete_M_two_mean_prices (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
 OriginalKCompleteMResidualSource.actualCompleteMSourceKPrice c h=actualGreenKMeanDebtPrice c h ∧
 OriginalKCompleteMResidualSource.actualCompleteMSourceFKPrice c h=actualGreenFKMeanDebtPrice c h :=by
 have means:=actual_original_two_gap_mean_prices c
 unfold OriginalKCompleteMResidualSource.actualCompleteMSourceKPrice OriginalKCompleteMResidualSource.actualCompleteMSourceFKPrice
 rw [means.1,means.2]
 exact ⟨rfl,rfl⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The actual original M whole-source action meets its independent two physical consumers with both mean fees paid by the actual Green sources. -/
theorem actual_original_M_source_mean_consumers (h : ℝ) :
 OriginalKSeedPhysicalRSource.actualSeedNativeKMeanPrice observation nontrivial half h=
  actualGreenKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h ∧
 OriginalKSeedPhysicalRSource.actualSeedNativeFKMeanPrice observation nontrivial half h=
  actualGreenFKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h :=by
 have source:=OriginalKCompleteMResidualSource.actual_complete_M_residual_prices observation nontrivial half h
 have mean:=actual_complete_M_two_mean_prices (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h
 exact ⟨source.1.trans mean.1,source.2.trans mean.2⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapKernelGreenSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
