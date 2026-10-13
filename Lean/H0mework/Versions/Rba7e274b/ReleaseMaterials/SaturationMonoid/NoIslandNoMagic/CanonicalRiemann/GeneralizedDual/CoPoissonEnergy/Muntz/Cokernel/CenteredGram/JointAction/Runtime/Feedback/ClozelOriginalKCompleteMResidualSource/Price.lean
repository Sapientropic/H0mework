import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteMResidualSource.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMResidualSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance completeMResidualPriceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "μ" => FiniteMobiusResolventFlux.actualMean
local notation "q" => (1/4:ℝ)

def actualMeanZeroGapCoefficient (c : BurnolCompletedMellinCoordinate) : ℂ :=
 (1/2:ℂ)*((((2*q:ℝ):ℂ)*(q:ℂ)^(-c.value))/(c.value/2-1/2))+
  (2:ℂ)*star (burnolMellinGapMoment (OriginalKQuarterTailPhysicalSource.actualStarSource c).value)

def actualCompleteMSourceKPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c)*
 (actualMSourceTateInventory c h*(-2*OriginalKStaticKernelSourceGramSource.actualDualKernelGram c+
   actualMeanZeroGapCoefficient c*star (μ (K c:BurnolL2)))-
  (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*actualMSourceVCoefficient c h)*
   OriginalKStaticKernelSourceGramSource.actualDualKernelGram c-
  (2*actualPositionMSourceMass c h)*star (μ (K c:BurnolL2))-
  (2*actualFourierMSourceMass c h)*star (μ (fourierL2 (K c:BurnolL2))))
def actualCompleteMSourceFKPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c)*
 (actualMSourceTateInventory c h*(-2*OriginalKStaticKernelSourceGramSource.actualFourierDualGram c+
   actualMeanZeroGapCoefficient c*star (μ (fourierL2 (K c:BurnolL2))))-
  (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*actualMSourceVCoefficient c h)*
   OriginalKStaticKernelSourceGramSource.actualFourierDualGram c-
  (2*actualPositionMSourceMass c h)*star (μ (fourierL2 (K c:BurnolL2)))-
  (2*actualFourierMSourceMass c h)*star (μ (K c:BurnolL2)))

/-- The complete actual M source field is read on its two original physical feet; self/Fourier-self costs have left the field. -/
theorem actual_two_complete_M_source_prices (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
 inner ℂ (K c) ((OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c) •
  actualCompleteMSourceInventoryField c h)=actualCompleteMSourceKPrice c h ∧
 inner ℂ (Fphysical (K c)) ((OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c) •
  actualCompleteMSourceInventoryField c h)=actualCompleteMSourceFKPrice c h :=by
 have Gram:=OriginalKStaticKernelSourceGramSource.actual_original_static_source_Gram_feet c
 have means:=OriginalKStaticKernelSourceGramSource.actual_static_G_FG_input_prices c
 unfold actualCompleteMSourceInventoryField actualMeanZeroCompactRField
 simp only [inner_smul_right,inner_add_right,inner_sub_right]
 have dual : inner ℂ (K c) (K (OriginalKQuarterTailPhysicalSource.actualStarSource c))=
  OriginalKStaticKernelSourceGramSource.actualDualKernelGram c :=Gram.2.1
 have Fdual : inner ℂ (Fphysical (K c)) (K (OriginalKQuarterTailPhysicalSource.actualStarSource c))=
  OriginalKStaticKernelSourceGramSource.actualFourierDualGram c :=rfl

 rw [dual,Fdual,means.1,means.2.1,means.2.2.1,means.2.2.2]
 exact ⟨rfl,rfl⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The original complete M consumes its generated residual inventory through the same whole action before the independent character reads it. -/
theorem actual_complete_M_residual_prices (h : ℝ) :
 OriginalKSeedPhysicalRSource.actualSeedNativeKMeanPrice observation nontrivial half h=
  actualCompleteMSourceKPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h ∧
 OriginalKSeedPhysicalRSource.actualSeedNativeFKMeanPrice observation nontrivial half h=
  actualCompleteMSourceFKPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h :=by
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have prior:=OriginalKSeedPhysicalRSource.actual_complete_seed_native_M_prices observation nontrivial half h
 have static:=OriginalKStaticKernelSourceGramSource.actual_static_source_complete_M_prices observation nontrivial half h
 have whole:OriginalKCoupledPhysicalRFieldSource.actualWeightedMResponseField c h=
  (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c) •
   actualCompleteMSourceInventoryField c h :=by
  rw [OriginalKSeedPhysicalRSource.actual_complete_seed_native_M_field,
   actual_complete_M_residual_source,actual_complete_M_source_inventory]
 have read:=actual_two_complete_M_source_prices c h
 have Kprice:OriginalKCoupledPhysicalRFieldSource.actualWeightedKMeanPrice observation nontrivial half h=actualCompleteMSourceKPrice c h :=by
  unfold OriginalKCoupledPhysicalRFieldSource.actualWeightedKMeanPrice
  dsimp only
  rw [whole]
  exact read.1
 have FKprice:OriginalKCoupledPhysicalRFieldSource.actualWeightedFKMeanPrice observation nontrivial half h=actualCompleteMSourceFKPrice c h :=by
  unfold OriginalKCoupledPhysicalRFieldSource.actualWeightedFKMeanPrice
  dsimp only
  rw [whole]
  exact read.2
 exact ⟨prior.1.symm.trans (static.1.symm.trans Kprice),prior.2.symm.trans (static.2.symm.trans FKprice)⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMResidualSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
