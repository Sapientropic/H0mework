import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactJordanRankSource.Mean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactJordanRankSource
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

local instance compactJordanPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualTailRPrice (coordinate : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) : ℂ :=
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical
 let foot:=star (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate)*
  inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
  (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)
 (-2:ℂ)*star (OriginalKFourierKernelDependentRAction.actualNativeKernelCoefficient coordinate)*
  (-(coordinate.value-1)/2*
   (star (1/z^2)*(1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)+
    inner ℂ (OriginalKJordanSeedFieldSource.actualJordanSeedExterior z) (Fphysical : BurnolL2))+
   (2/(coordinate.value-1):ℂ)*foot)-
 ((8:ℂ)*burnolMellinGapMoment coordinate.value/(coordinate.value-1))*foot

/-- Whole raw tail R action is priced on the receiver own Fourier face; all native Jordan exterior and original input costs remain. -/
theorem actual_tail_R_physical_price (coordinate : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) :
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 inner ℂ (burnolDirectRightResolvent (dual.value/2) (burnolRadiusNormalizedUnitTail dual q (by norm_num)))
  (fourierL2 (physical : BurnolL2))=actualTailRPrice coordinate physical :=by
 dsimp only
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical
 have right:1/4<z.re:=by
  dsimp only [z]
  rw [Complex.div_re];norm_num;linarith [dual.rightHalf]
 rw [actual_quarter_tail_whole_R,inner_add_left,inner_smul_left,inner_smul_left]
 rw [OriginalKFourierKernelDependentRAction.actual_resonant_native_field_price coordinate physical]
 have jPrice:=OriginalKJordanSeedFieldSource.actual_jordan_seed_physical_price z right Fphysical
 change inner ℂ (OriginalKFourierKernelDependentRAction.actualResonantField z Native.seed)
  (fourierL2 (physical : BurnolL2))=_ at jPrice
 rw [jPrice]
 unfold OriginalKConstantSeedWholeRAction.actualWholeSeedRField
 have dualTwice:∀ native:BurnolCompletedMellinCoordinate,
  OriginalKQuarterTailPhysicalSource.actualStarSource (OriginalKQuarterTailPhysicalSource.actualStarSource native)=native:=by
  intro native
  cases native
  unfold OriginalKQuarterTailPhysicalSource.actualStarSource
  dsimp only
  congr 1
  exact star_star _
 have twice:OriginalKQuarterTailPhysicalSource.actualStarSource dual=coordinate:=dualTwice coordinate
 rw [twice,inner_smul_left,inner_add_left]
 have edge:=OriginalKConstantSeedWholeRAction.actual_edge_physical_input_price coordinate Fphysical
 have seed:=OriginalKConstantContactSourceAction.actual_constant_seed_input_price Fphysical
 change inner ℂ (OriginalRieszFiniteSource.edgePrimitive coordinate) (fourierL2 (physical : BurnolL2))=_ at edge
 change inner ℂ Native.seed (fourierL2 (physical : BurnolL2))=_ at seed
 rw [edge,seed]
 unfold actualTailRPrice
 dsimp only [z,dual,Fphysical]
 have faceRead:(evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical : BurnolL2)=
  fourierL2 (physical : BurnolL2):=rfl
 rw [faceRead]
 simp only [OriginalKQuarterTailPhysicalSource.actualStarSource,starRingEnd_apply,star_mul,star_neg,
  star_div₀,star_sub,star_one,star_ofNat,star_star]
 ring

def actualCompactJordanPrice (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2)
 (physical : BurnolPaAmbientCarrier) : ℂ :=
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical
 (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)*star (actualSecondMean coordinate source)+
 star (OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual (actualFirstCut coordinate source))*
  (-(2:ℂ)*inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
   (2:ℂ)*burnolMellinGapMoment coordinate.value*Paid.actualMean (Fphysical : BurnolL2))+
 star (OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual source)*actualTailRPrice coordinate physical

/-- Actual second source rank and mean equations eliminate the independent whole Jordan price. -/
theorem actual_compact_Jordan_physical_price (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2)
 (compact : originalPhysicalCutoff q source=source) (even : reflectL2 source=source)
 (physical : BurnolPaAmbientCarrier) :
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 inner ℂ (OriginalKFourierKernelDependentRAction.actualResonantField (dual.value/2) source)
  (fourierL2 (physical : BurnolL2))=actualCompactJordanPrice coordinate source physical :=by
 dsimp only
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical
 rw [actual_compact_Jordan_rank_source coordinate source compact even,inner_add_left,inner_add_left,
  inner_smul_left,inner_smul_left]
 have quarter:=congrArg (starRingEnd ℂ) (paid172QuarterPhysicalPrice Fphysical
  (burnolDirectRightResolvent (dual.value/2) (actualFirstCut coordinate source)))
 simp only [inner_conj_symm] at quarter
 rw [map_mul,map_mul,map_div₀,map_one,map_ofNat] at quarter
 simp only [starRingEnd_apply,star_star] at quarter
 change inner ℂ (originalPhysicalCutoff q (burnolDirectRightResolvent (dual.value/2)
  (actualFirstCut coordinate source))) (fourierL2 (physical : BurnolL2))=_ at quarter
 rw [actual_second_R_mean coordinate source compact even] at quarter
 have tail:=OriginalKCompactAdjointRSource.actual_compact_tail_physical_price coordinate Fphysical
 change inner ℂ (burnolRadiusNormalizedUnitTail dual q (by norm_num)) (fourierL2 (physical : BurnolL2))=_ at tail
 rw [quarter,tail]
 have whole:=actual_tail_R_physical_price coordinate physical
 dsimp only at whole
 rw [actual_quarter_tail_whole_R] at whole
 change _=actualCompactJordanPrice coordinate source physical
 unfold actualCompactJordanPrice
 dsimp only
 rw [whole]
 simp only [starRingEnd_apply]
 rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactJordanRankSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
