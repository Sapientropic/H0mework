import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactAdjointRSource.Physical
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactAdjointRSource
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



local instance compactMeanColumnPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualCompactFourierResponsePrice (coordinate : BurnolCompletedMellinCoordinate)
 (source : BurnolL2) (physical : BurnolPaAmbientCarrier) : ℂ :=
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let coefficient:=actualCompactTailCoefficient dual source
 let mean:=(coefficient*(((2*q:ℝ):ℂ)*(q:ℂ)^(-dual.value))-Paid.actualMean source)/(dual.value/2-1/2)
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical
 (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)*star mean+
 star coefficient*(-(2:ℂ)*inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
   (2:ℂ)*burnolMellinGapMoment coordinate.value*Paid.actualMean (Fphysical : BurnolL2))

/-- Actual compact source action, not a free Fourier price: adjoint, rank and FTC meet the receiver's own two physical faces. -/
theorem actual_compact_F_R_source_price (coordinate : BurnolCompletedMellinCoordinate)
 (source : BurnolL2) (compact : originalPhysicalCutoff q source=source) (even : reflectL2 source=source)
 (physical : BurnolPaAmbientCarrier) :
 inner ℂ (fourierL2 source) (burnolDirectRightResolvent (coordinate.value/2) (physical : BurnolL2))=
 actualCompactFourierResponsePrice coordinate source physical := by
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical
 let acted:=burnolDirectRightResolvent (dual.value/2) source
 rw [actual_compact_F_R_physical_action,actual_compact_R_rank_source dual source compact even,
   inner_add_left,inner_smul_left]
 have quarter:=congrArg (starRingEnd ℂ) (paid172QuarterPhysicalPrice Fphysical acted)
 simp only [inner_conj_symm] at quarter
 rw [map_mul,map_mul,map_div₀,map_one,map_ofNat] at quarter
 simp only [starRingEnd_apply,star_star] at quarter
 change inner ℂ (originalPhysicalCutoff q acted) (Fphysical : BurnolL2)=
   (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)*star (Paid.actualMean acted) at quarter
 change inner ℂ (originalPhysicalCutoff q acted) (Fphysical : BurnolL2)+
   star (actualCompactTailCoefficient dual source)*
     inner ℂ (burnolRadiusNormalizedUnitTail dual q (by norm_num)) (Fphysical : BurnolL2)=_
 rw [quarter,actual_compact_quarter_mean_price dual source compact even,
   actual_compact_tail_physical_price coordinate Fphysical]
 rfl

/-- The actual original columns are their own q zero extensions and source even/mean-zero qualified carriers. -/
theorem actual_original_UV_compact_even :
 originalPhysicalCutoff q OriginalRieszSource.Response.wholeU=OriginalRieszSource.Response.wholeU ∧
 reflectL2 OriginalRieszSource.Response.wholeU=OriginalRieszSource.Response.wholeU ∧
 originalPhysicalCutoff q OriginalRieszSource.Response.wholeV=OriginalRieszSource.Response.wholeV ∧
 reflectL2 OriginalRieszSource.Response.wholeV=OriginalRieszSource.Response.wholeV := by
 refine ⟨?_,OriginalRieszSource.Response.wholeU_reflection,?_,OriginalRieszSource.Response.wholeV_reflection⟩
 · change burnolRadiusZeroExtension q (burnolRadiusRestriction q
     (burnolRadiusZeroExtension q (OriginalRieszSource.Response.u : BurnolQuarterIntervalL2)))=_
   rw [burnolRadiusRestriction_zeroExtension]
   rfl
 · change burnolRadiusZeroExtension q (burnolRadiusRestriction q
     (burnolRadiusZeroExtension q (OriginalRieszSource.Response.v : BurnolQuarterIntervalL2)))=_
   rw [burnolRadiusRestriction_zeroExtension]
   rfl

theorem actual_original_UV_F_R_source_prices (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 inner ℂ (fourierL2 OriginalRieszSource.Response.wholeU)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (material : BurnolL2))=
 actualCompactFourierResponsePrice coordinate OriginalRieszSource.Response.wholeU material ∧
 inner ℂ (fourierL2 OriginalRieszSource.Response.wholeV)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (material : BurnolL2))=
 actualCompactFourierResponsePrice coordinate OriginalRieszSource.Response.wholeV material := by
 have qualified:=actual_original_UV_compact_even
 exact ⟨actual_compact_F_R_source_price _ _ qualified.1 qualified.2.1 _,
   actual_compact_F_R_source_price _ _ qualified.2.2.1 qualified.2.2.2 _⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactAdjointRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
