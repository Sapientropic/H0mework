import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceReturnGramAction.Return
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceScaledMaximalResponse
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
open OriginalRieszSource
local instance wardAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def originalFourierDisplacement (h : ℝ) : BurnolL2 :=
 burnolMultiplicativeDilation h
   (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))-
 fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
def originalMixedEnergy (h : ℝ) : ℂ :=
 inner ℂ (originalFourierDisplacement observation nontrivial half h)
   (OriginalKFiniteWardGram.displacement (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h)

private theorem original_inverse_inner (h : ℝ) (left right : BurnolL2) :
 inner ℂ (burnolMultiplicativeDilation h left) right=
 inner ℂ left (burnolMultiplicativeDilation (-h) right) := by
 have source:=(burnolMultiplicativeDilation h).inner_map_map left (burnolMultiplicativeDilation (-h) right)
 rw [burnolMultiplicativeDilation_add,add_neg_cancel,burnolMultiplicativeDilation_zero] at source
 exact source

theorem actual_original_mixed_energy_ward (h : ℝ) :
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (originalForcingPair observation nontrivial half h)=
 (2:ℂ)*(1-pairedMellinTranslationCharacter (star observation.coordinate) h)*
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)-
 originalMixedEnergy observation nontrivial half h := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have native:=actual_original_K_finite_pair observation nontrivial half h
 have generated:=congrArg (fun material : BurnolL2=>inner ℂ
   (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) material) native
 unfold pairedBurnolMultiplicativeDilation at generated
 simp only [smul_apply,add_apply,inner_smul_right,inner_add_right] at generated
 unfold originalMixedEnergy originalFourierDisplacement
 rw [OriginalKFiniteWardGram.displacement_action,inner_sub_left,inner_sub_right,inner_sub_right,
   (burnolMultiplicativeDilation h).inner_map_map,original_inverse_inner]
 unfold pairedMellinTranslationCharacter at generated
 change (1/2:ℂ)*(inner ℂ _ (burnolMultiplicativeDilation h _)+inner ℂ _ (burnolMultiplicativeDilation (-h) _))=
   ((fullMellinTranslationCharacter (star observation.coordinate) h+reciprocalMellinTranslationCharacter (star observation.coordinate) h)/2)*inner ℂ _ _+
   (1/2:ℂ)*inner ℂ _ _ at generated
 unfold pairedMellinTranslationCharacter
 linear_combination -2*generated

theorem actual_original_K_energy_ward (h : ℝ) :
 inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (originalForcingPair observation nontrivial half h)=
 (2:ℂ)*(1-pairedMellinTranslationCharacter (star observation.coordinate) h)*
 OriginalRieszFinitePairing.kernelSelfSource (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)-
 OriginalKFiniteWardGram.sourceEnergy (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h := by
 exact OriginalKFiniteWardGram.source_force_energy_ward _ h

def primitiveProjectionStock (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : BurnolL2 :=
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • primitiveFiniteAction observation nontrivial half h+
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • (Return.sourceA observation • Paid.actualMovedOutsideRStock observation nontrivial half h)+
 Return.sourceA observation • Paid.actualOriginalWaveRStock observation nontrivial half h nonnegative bounded+
 Return.sourceA observation • Paid.actualOutsideRResponseStock observation nontrivial half h

def originalKForcingWard (h : ℝ) : ℂ :=
 (2:ℂ)*(1-pairedMellinTranslationCharacter (star observation.coordinate) h)*
 OriginalRieszFinitePairing.kernelSelfSource (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)-
 OriginalKFiniteWardGram.sourceEnergy (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h

def originalFKForcingWard (h : ℝ) : ℂ :=
 (2:ℂ)*(1-pairedMellinTranslationCharacter (star observation.coordinate) h)*
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)-
 originalMixedEnergy observation nontrivial half h

/-- Both forcing prices are generated by the same K finite source action, before the residual stock is read. -/
theorem actual_scaled_kernel_cross_ward (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 Return.sourceA observation*Paid.originalKernelCross observation nontrivial half h=
 characterPrice*star a*star (originalKForcingWard observation nontrivial half h+originalFKForcingWard observation nontrivial half h)-
 star characterPrice*a*(originalKForcingWard observation nontrivial half h-originalFKForcingWard observation nontrivial half h)-
 characterPrice*Paid.originalPairKernelRead observation nontrivial half (primitiveProjectionStock observation nontrivial half h nonnegative bounded)+
 star characterPrice*Paid.originalSiblingKernelRead observation nontrivial half (primitiveProjectionStock observation nontrivial half h nonnegative bounded) := by
 dsimp only
 have generated:=actual_scaled_original_kernel_cross observation nontrivial half h nonnegative bounded
 dsimp only at generated
 rw [generated,actual_scaled_source_finite_inventory]
 change _ = _
 have stock : -OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h • originalForcingPair observation nontrivial half h+
   (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • primitiveFiniteAction observation nontrivial half h+
   (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • (Return.sourceA observation • Paid.actualMovedOutsideRStock observation nontrivial half h)+
   Return.sourceA observation • Paid.actualOriginalWaveRStock observation nontrivial half h nonnegative bounded+
   Return.sourceA observation • Paid.actualOutsideRResponseStock observation nontrivial half h=
   -OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h • originalForcingPair observation nontrivial half h+
   primitiveProjectionStock observation nontrivial half h nonnegative bounded := by
   unfold primitiveProjectionStock
   module
 rw [stock]
 rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
   OriginalKPairedResponseGramAction.original_kernel_sibling_qualification,
   OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
   OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
 simp only [inner_add_right,inner_smul_right,neg_mul,star_add,star_neg,star_mul]
 rw [actual_original_K_energy_ward,actual_original_mixed_energy_ward]
 unfold originalKForcingWard originalFKForcingWard
 ring


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceScaledMaximalResponse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
