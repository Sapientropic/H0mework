import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedResponseGramAction.Boundary
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
local instance responseAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
theorem actual_original_paired_source_coupling (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 Q (ActionSource.pairedResponse observation nontrivial half h)=
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • Q (OriginalKCombCofinalPaAction.paired (originalBoundaryRResponse observation nontrivial half h nonnegative bounded))-
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)) • Q (OriginalKCombCofinalPaAction.paired (originalKernelRResponse observation nontrivial half))+
 Q (OriginalKCombCofinalPaAction.paired (actualPaRResponseStock observation nontrivial half h))+
 Q (OriginalKCombCofinalPaAction.paired (actualOutsideRResponseStock observation nontrivial half h)) := by
 have generated:=congrArg (fun material : BurnolL2=>Q (OriginalKCombCofinalPaAction.paired material))
   (actual_original_R_source_coupling observation nontrivial half h nonnegative bounded)
 unfold OriginalKFullSourceRResponse.pairedResponse
 unfold OriginalKCombCofinalPaAction.paired at generated ⊢
 simp only [map_add,map_sub,map_smul] at generated ⊢
 convert! generated using 1
 module

theorem actual_original_sibling_source_coupling (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 Q (ActionSource.siblingResponse observation nontrivial half h)=
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) • Q (OriginalKCombCofinalPaAction.sibling (originalBoundaryRResponse observation nontrivial half h nonnegative bounded))-
 (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)) • Q (OriginalKCombCofinalPaAction.sibling (originalKernelRResponse observation nontrivial half))+
 Q (OriginalKCombCofinalPaAction.sibling (actualPaRResponseStock observation nontrivial half h))+
 Q (OriginalKCombCofinalPaAction.sibling (actualOutsideRResponseStock observation nontrivial half h)) := by
 have generated:=congrArg (fun material : BurnolL2=>Q (OriginalKCombCofinalPaAction.sibling material))
   (actual_original_R_source_coupling observation nontrivial half h nonnegative bounded)
 unfold OriginalKFullSourceRResponse.siblingResponse
 unfold OriginalKCombCofinalPaAction.sibling at generated ⊢
 simp only [map_add,map_sub,map_smul] at generated ⊢
 convert! generated using 1
 module

def originalPairKernelRead (material : BurnolL2) : ℂ :=
 let k:=burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 inner ℂ (Q (OriginalKCombCofinalPaAction.paired material)) (k+Fphysical k)
def originalSiblingKernelRead (material : BurnolL2) : ℂ :=
 let k:=burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 inner ℂ (k-Fphysical k) (Q (OriginalKCombCofinalPaAction.sibling material))

/-- The original character cross price consumes the genuine four response stocks. -/
theorem actual_original_kernel_cross_response (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 let coefficient:=2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let characterPrice:=coefficient*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 originalKernelCross observation nontrivial half h=
 characterPrice*(star coefficient*originalPairKernelRead observation nontrivial half (originalBoundaryRResponse observation nontrivial half h nonnegative bounded)-
   star characterPrice*originalPairKernelRead observation nontrivial half (originalKernelRResponse observation nontrivial half)+
   originalPairKernelRead observation nontrivial half (actualPaRResponseStock observation nontrivial half h)+
   originalPairKernelRead observation nontrivial half (actualOutsideRResponseStock observation nontrivial half h))+
 star characterPrice*(coefficient*originalSiblingKernelRead observation nontrivial half (originalBoundaryRResponse observation nontrivial half h nonnegative bounded)-
   characterPrice*originalSiblingKernelRead observation nontrivial half (originalKernelRResponse observation nontrivial half)+
   originalSiblingKernelRead observation nontrivial half (actualPaRResponseStock observation nontrivial half h)+
   originalSiblingKernelRead observation nontrivial half (actualOutsideRResponseStock observation nontrivial half h)) := by
 unfold originalKernelCross originalPairKernelRead originalSiblingKernelRead
 dsimp only
 rw [actual_original_paired_source_coupling observation nontrivial half h nonnegative bounded,
   actual_original_sibling_source_coupling observation nontrivial half h nonnegative bounded]
 simp only [inner_add_left,inner_sub_left,inner_add_right,inner_sub_right,inner_smul_left,inner_smul_right,starRingEnd_apply]
 ring

private theorem Q_native_left_read (left : BurnolPaOrthogonalCarrier) (material : BurnolL2) :
 inner ℂ (left : BurnolPaAmbientCarrier) (Q material)=inner ℂ (left : BurnolL2) material := by
 have low:=burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.inner_orthogonalProjectionOnto_eq_of_mem_left left (P material)
 have physical:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left (left : BurnolPaAmbientCarrier) material
 exact low.trans physical

private theorem original_kernel_fourier_twice :
 fourierL2 (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))=
 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2) := by
 rw [fourierL2_fourierL2]
 exact mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)).property.2

theorem original_kernel_paired_qualification (material : BurnolL2) :
 originalPairKernelRead observation nontrivial half material=
 star (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2) material+
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)) material) := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let k : BurnolPaOrthogonalCarrier:=⟨burnolCompletedMellinRieszVector coordinate,
   riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate observation.mathlibZero⟩
 let fk:=burnolCompactCoPoissonActionSquare.orthogonalAction k
 have first:=Q_native_left_read k (OriginalKCombCofinalPaAction.paired material)
 have second:=Q_native_left_read fk (OriginalKCombCofinalPaAction.paired material)
 have moved:=fourierL2.inner_map_map (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) material
 rw [original_kernel_fourier_twice observation nontrivial half] at moved
 have movedOther:=fourierL2.inner_map_map (burnolCompletedMellinRieszVector coordinate : BurnolL2) material
 unfold originalPairKernelRead
 dsimp only
 rw [inner_add_right,
   ←inner_conj_symm (Q (OriginalKCombCofinalPaAction.paired material)) (burnolCompletedMellinRieszVector coordinate),
   ←inner_conj_symm (Q (OriginalKCombCofinalPaAction.paired material)) (Fphysical (burnolCompletedMellinRieszVector coordinate))]
 change star (inner ℂ (k : BurnolPaAmbientCarrier) (Q (OriginalKCombCofinalPaAction.paired material)))+
   star (inner ℂ (fk : BurnolPaAmbientCarrier) (Q (OriginalKCombCofinalPaAction.paired material)))=_
 rw [first,second]
 change star (inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) (OriginalKCombCofinalPaAction.paired material))+
   star (inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) (OriginalKCombCofinalPaAction.paired material))=_
 unfold OriginalKCombCofinalPaAction.paired
 simp only [inner_smul_right,inner_add_right]
 rw [moved,movedOther]
 simp only [star_add,star_mul,star_div₀,star_one,star_ofNat]
 ring

theorem original_kernel_sibling_qualification (material : BurnolL2) :
 originalSiblingKernelRead observation nontrivial half material=
 inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2) material-
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)) material := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let k : BurnolPaOrthogonalCarrier:=⟨burnolCompletedMellinRieszVector coordinate,
   riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate observation.mathlibZero⟩
 let fk:=burnolCompactCoPoissonActionSquare.orthogonalAction k
 have first:=Q_native_left_read k (OriginalKCombCofinalPaAction.sibling material)
 have second:=Q_native_left_read fk (OriginalKCombCofinalPaAction.sibling material)
 have moved:=fourierL2.inner_map_map (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) material
 rw [original_kernel_fourier_twice observation nontrivial half] at moved
 have movedOther:=fourierL2.inner_map_map (burnolCompletedMellinRieszVector coordinate : BurnolL2) material
 unfold originalSiblingKernelRead
 dsimp only
 rw [inner_sub_left]
 change inner ℂ (k : BurnolPaAmbientCarrier) (Q (OriginalKCombCofinalPaAction.sibling material))-
   inner ℂ (fk : BurnolPaAmbientCarrier) (Q (OriginalKCombCofinalPaAction.sibling material))=_
 rw [first,second]
 change inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) (OriginalKCombCofinalPaAction.sibling material)-
   inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) (OriginalKCombCofinalPaAction.sibling material)=_
 unfold OriginalKCombCofinalPaAction.sibling
 simp only [inner_smul_right,inner_sub_right]
 rw [moved,movedOther]
 ring

theorem actual_paired_Pa_kernel_price (h : ℝ) :
 originalPairKernelRead observation nontrivial half (actualPaRResponseStock observation nontrivial half h)=
 star (burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (actualPaSourceStock observation nontrivial half h)*
 (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)+
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4))) := by
 rw [original_kernel_paired_qualification,actual_Pa_R_kernel_inventory,actual_Pa_R_fourier_kernel_inventory]
 congr 1
 ring

theorem actual_sibling_Pa_kernel_price (h : ℝ) :
 originalSiblingKernelRead observation nontrivial half (actualPaRResponseStock observation nontrivial half h)=
 burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (actualPaSourceStock observation nontrivial half h)*
 (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)-
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)) := by
 rw [original_kernel_sibling_qualification,actual_Pa_R_kernel_inventory,actual_Pa_R_fourier_kernel_inventory]
 ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedResponseGramAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
