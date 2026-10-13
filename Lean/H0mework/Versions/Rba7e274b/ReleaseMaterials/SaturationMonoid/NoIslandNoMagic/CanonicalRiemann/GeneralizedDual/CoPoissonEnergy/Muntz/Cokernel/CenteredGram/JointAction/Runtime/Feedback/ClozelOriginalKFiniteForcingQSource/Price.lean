import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteForcingQSource.Return
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteForcingQSource
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
local instance priceAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def finitePaPairPrice (h : ℝ) : ℂ :=
 star (burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
   (actualFinitePaStock observation nontrivial half h)*
  (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
    (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)+
   inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
    (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)))

def finitePaSiblingPrice (h : ℝ) : ℂ :=
 burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
   (actualFinitePaStock observation nontrivial half h)*
  (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
    (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)-
   inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
    (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4))

/-- The original character consumer reads the actual finite R source, both generated Pa unit prices, and the un-erased outside cost. -/
theorem actual_finite_source_character_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
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
   A*finitePaPairPrice observation nontrivial half h-
   A*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
     (OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualFiniteOutsideStock observation nontrivial half h)))+
 star characterPrice*((2*a)*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
   A*finitePaSiblingPrice observation nontrivial half h+
   A*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
     (OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualFiniteOutsideStock observation nontrivial half h))) := by
 dsimp only
 have old:=OriginalKSourceScaledMaximalResponse.actual_scaled_complete_response observation nontrivial half h nonnegative bounded
 change OriginalKSourceScaledMaximalResponse.Return.sourceA observation •
   OriginalKFullSourceRResponse.Op.R observation nontrivial half (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)=
   OriginalKSourceScaledMaximalResponse.scaledMaximalSource observation nontrivial half h nonnegative bounded at old
 have source:=OriginalKSourceScaledMaximalResponse.actual_scaled_original_kernel_cross observation nontrivial half h nonnegative bounded
 dsimp only at source
 rw [←old,actual_scaled_R_finite_source observation nontrivial half h nonnegative bounded] at source
 rw [source]
 rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
   OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
 simp only [inner_add_right,inner_sub_right,inner_smul_right,star_add,star_sub,star_mul,
   OriginalKSourceScaledMaximalResponse.actual_sourceA_star,star_neg,star_ofNat]
 have Pa:=actual_R_finite_Pa_prices observation nontrivial half h
 rw [OriginalKSourceScaledMaximalResponse.actual_original_K_energy_ward,
   OriginalKSourceScaledMaximalResponse.actual_original_mixed_energy_ward,Pa.1,Pa.2]
 unfold finitePaPairPrice finitePaSiblingPrice
 rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
   OriginalKPairedResponseGramAction.original_kernel_sibling_qualification,
   OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
   OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
 unfold OriginalKSourceScaledMaximalResponse.originalKForcingWard OriginalKSourceScaledMaximalResponse.originalFKForcingWard
 simp only [star_add,star_sub,star_mul]
 ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteForcingQSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
