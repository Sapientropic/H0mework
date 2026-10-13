import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKInsideDebtRAction.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKInsideDebtRSource
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalRieszFiniteSource OriginalRieszFiniteColumns OriginalRieszFinitePairing OriginalPaPhysicalGreen
local instance priceInsideDebtAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
namespace Full
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalCommonInverseForcing.SourceJoint.FullStock
 (meanDebt actual_inside_mean_debt)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalCommonInverseForcing.SourceJoint
 (upperSeedFactor upperSourceWave upperSourceField upperSourceCorrection actual_upper_common_seed)
end Full
namespace Prior
export OriginalKFiniteForcingQSource (actualFinitePaStock actualFiniteOutsideStock actual_finite_source_character_price)
export OriginalKSourceScaledMaximalResponse (originalForcingPair)
end Prior
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualWavePaPairPrice (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : ℂ :=
 star (burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
   (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient
     (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded)*
  (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
    (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)+
   inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
    (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)))

def actualWavePaSiblingPrice (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : ℂ :=
 burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
   (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient
     (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded)*
  (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
    (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)-
   inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
    (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4))

/-- The original character price consumes the generated rank/opposite response and literal actual wave Pa stock. -/
theorem actual_rank_generated_character_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 let a:=Full.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 A*OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h=
 characterPrice*star a*star
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h+
    OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h)-
 star characterPrice*a*
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h-
    OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h)-
 characterPrice*((2*star a)*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)-
   A*actualWavePaPairPrice observation nontrivial half h nonnegative bounded-
   A*star a*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
     (actualInsideNativeREffect observation nontrivial half h))+
 star characterPrice*((2*a)*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
   A*actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded+
   A*a*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
     (actualInsideNativeREffect observation nontrivial half h)) := by
 dsimp only
 have source:=Prior.actual_finite_source_character_price observation nontrivial half h nonnegative bounded
 dsimp only at source
 rw [actual_original_R_inside_stock observation nontrivial half h nonnegative bounded] at source
 have pair (coefficient : ℂ) (material : BurnolL2) :
   OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half (coefficient • material)=
   star coefficient*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half material := by
  rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
    OriginalKPairedResponseGramAction.original_kernel_paired_qualification]
  simp only [inner_smul_right,star_add,star_mul]
  ring
 have sibling (coefficient : ℂ) (material : BurnolL2) :
   OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half (coefficient • material)=
   coefficient*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half material := by
  rw [OriginalKPairedResponseGramAction.original_kernel_sibling_qualification,
    OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
  simp only [inner_smul_right]
  ring
 rw [pair,sibling] at source
 have native : OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (actualInsideDebt observation nontrivial half h)=actualInsideNativeREffect observation nontrivial half h :=
  (actual_original_R_inside_effect observation nontrivial half h).trans
   (actual_complete_inside_R_action observation nontrivial half h nonnegative)
 rw [native] at source
 unfold OriginalKFiniteForcingQSource.finitePaPairPrice OriginalKFiniteForcingQSource.finitePaSiblingPrice at source
 rw [actual_original_Pa_wave_stock observation nontrivial half h nonnegative bounded] at source
 unfold actualWavePaPairPrice actualWavePaSiblingPrice
 linear_combination source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKInsideDebtRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
