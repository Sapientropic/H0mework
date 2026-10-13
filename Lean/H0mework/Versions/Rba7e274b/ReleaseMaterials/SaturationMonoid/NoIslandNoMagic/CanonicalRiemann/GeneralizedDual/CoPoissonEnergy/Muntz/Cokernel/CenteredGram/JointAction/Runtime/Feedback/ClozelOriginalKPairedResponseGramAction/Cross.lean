import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedResponseGramAction.Response
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedResponseGramAction.Evolution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedResponseGramAction
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
local instance crossAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
/-- The largest source evolution is consumed before taking the original K/FK price. -/
theorem actual_maximal_kernel_cross (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 let coefficient:=2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let characterPrice:=coefficient*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let responsePrice:=coefficient*pairedMellinTranslationCharacter (star observation.coordinate) h
 originalKernelCross observation nontrivial half h=
 characterPrice*(star responsePrice*originalPairKernelRead observation nontrivial half (originalKernelRResponse observation nontrivial half)-
   star coefficient*originalPairKernelRead observation nontrivial half (pairedBurnolMultiplicativeDilation h (originalKernelRResponse observation nontrivial half))+
   star coefficient*originalPairKernelRead observation nontrivial half (actualMovedOutsideRStock observation nontrivial half h)+
   originalPairKernelRead observation nontrivial half (actualOriginalWaveRStock observation nontrivial half h nonnegative bounded)+
   originalPairKernelRead observation nontrivial half (actualOutsideRResponseStock observation nontrivial half h))+
 star characterPrice*(responsePrice*originalSiblingKernelRead observation nontrivial half (originalKernelRResponse observation nontrivial half)-
   coefficient*originalSiblingKernelRead observation nontrivial half (pairedBurnolMultiplicativeDilation h (originalKernelRResponse observation nontrivial half))+
   coefficient*originalSiblingKernelRead observation nontrivial half (actualMovedOutsideRStock observation nontrivial half h)+
   originalSiblingKernelRead observation nontrivial half (actualOriginalWaveRStock observation nontrivial half h nonnegative bounded)+
   originalSiblingKernelRead observation nontrivial half (actualOutsideRResponseStock observation nontrivial half h)) := by
 unfold originalKernelCross originalPairKernelRead originalSiblingKernelRead
 dsimp only
 unfold OriginalKFullSourceRResponse.pairedResponse OriginalKFullSourceRResponse.siblingResponse
 rw [actual_original_complete_response_evolution observation nontrivial half h nonnegative bounded]
 unfold OriginalKCombCofinalPaAction.paired OriginalKCombCofinalPaAction.sibling
 simp only [map_add,map_sub,map_smul,inner_add_left,inner_sub_left,inner_add_right,inner_sub_right,
   inner_smul_left,inner_smul_right,starRingEnd_apply,star_sub,star_mul,star_div₀,star_ofNat,star_one]
 ring

private theorem actual_wave_native_pairings (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (actualOriginalWaveRStock observation nontrivial half h nonnegative bounded)=
 burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (actualOriginalWaveStock observation nontrivial half h nonnegative bounded)*
 inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)) ∧
 (inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (actualOriginalWaveRStock observation nontrivial half h nonnegative bounded)=
 burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (actualOriginalWaveStock observation nontrivial half h nonnegative bounded)*
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)) := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have inside:actualOriginalWaveStock observation nontrivial half h nonnegative bounded ∈ burnolCompactCoPoissonClosedRange:=
   OriginalCommonInverseForcing.SourceJoint.actual_upper_ambient_inPa coordinate h nonnegative bounded
 let k : BurnolPaOrthogonalCarrier:=⟨burnolCompletedMellinRieszVector coordinate,
   riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate observation.mathlibZero⟩
 have left:=burnolPaResolvent_source_pairing coordinate (actualOriginalWaveStock observation nontrivial half h nonnegative bounded) inside k
 have right:=burnolPaResolvent_source_pairing coordinate (actualOriginalWaveStock observation nontrivial half h nonnegative bounded) inside
   (burnolCompactCoPoissonActionSquare.orthogonalAction k)
 change inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))
   (burnolDirectRightResolvent (coordinate.value/2) (actualOriginalWaveStock observation nontrivial half h nonnegative bounded : BurnolL2))=_ at right
 unfold actualOriginalWaveRStock
 rw [OriginalKCombCofinalRAction.original_R_direct]
 rw [OriginalKCombCofinalTwoDirection.coordinate_value] at left right
 exact ⟨left,right⟩

theorem actual_original_wave_pair_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 originalPairKernelRead observation nontrivial half (actualOriginalWaveRStock observation nontrivial half h nonnegative bounded)=
 star (burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (actualOriginalWaveStock observation nontrivial half h nonnegative bounded)*
 (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)+
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4))) := by
 have source:=actual_wave_native_pairings observation nontrivial half h nonnegative bounded
 rw [original_kernel_paired_qualification,source.1,source.2]
 congr 1
 ring

theorem actual_original_wave_sibling_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 originalSiblingKernelRead observation nontrivial half (actualOriginalWaveRStock observation nontrivial half h nonnegative bounded)=
 burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (actualOriginalWaveStock observation nontrivial half h nonnegative bounded)*
 (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)-
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)) := by
 have source:=actual_wave_native_pairings observation nontrivial half h nonnegative bounded
 rw [original_kernel_sibling_qualification,source.1,source.2]
 ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedResponseGramAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
