import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQuarterTailPhysicalSource.Source
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQuarterTailPhysicalSource
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

local instance tailPriceAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem actual_physical_source_price (physical : BurnolPaAmbientCarrier) (coordinate : BurnolCompletedMellinCoordinate) :
 inner ℂ (physical : BurnolL2) (burnolRadiusNormalizedUnitTail coordinate q (by norm_num))=
 -(2:ℂ)*inner ℂ physical (burnolCompletedMellinRieszVector (actualStarSource coordinate))+
 ((2:ℂ)*star (burnolMellinGapMoment (actualStarSource coordinate).value))*
   star (Paid.actualMean (physical : BurnolL2)) := by
 have projected:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
   |>.inner_orthogonalProjectionOnto_eq_of_mem_left physical
     (burnolRadiusNormalizedUnitTail coordinate q (by norm_num))
 rw [←projected]
 change inner ℂ physical (burnolEvenAmbientProjection (burnolRadiusNormalizedUnitTail coordinate q (by norm_num)))=_
 rw [actual_quarter_tail_physical_source,inner_add_right,inner_smul_right,inner_smul_right]
 have mean : inner ℂ physical OriginalRieszFiniteSynthesis.gapMeanVector=
   star (Paid.actualMean (physical : BurnolL2)) := by
  rw [←inner_conj_symm physical OriginalRieszFiniteSynthesis.gapMeanVector,OriginalRieszFiniteSynthesis.gapMeanVector_readback]
  rfl
 rw [mean]

def actualQuarterTailPairPrice : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let k:=burnolCompletedMellinRieszVector coordinate
 let dual:=burnolCompletedMellinRieszVector (actualStarSource coordinate)
 show ℂ from -(2:ℂ)*star (inner ℂ k dual+inner ℂ (evenFaceFourierEquiv burnolUnscaledCommonGapRadius k) dual)+
 ((2:ℂ)*burnolMellinGapMoment (actualStarSource coordinate).value)*
 (Paid.actualMean (k : BurnolL2)+Paid.actualMean (fourierL2 (k : BurnolL2)))

def actualQuarterTailSiblingPrice : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let k:=burnolCompletedMellinRieszVector coordinate
 let dual:=burnolCompletedMellinRieszVector (actualStarSource coordinate)
 show ℂ from -(2:ℂ)*(inner ℂ k dual-inner ℂ (evenFaceFourierEquiv burnolUnscaledCommonGapRadius k) dual)+
 ((2:ℂ)*star (burnolMellinGapMoment (actualStarSource coordinate).value))*
 (star (Paid.actualMean (k : BurnolL2))-star (Paid.actualMean (fourierL2 (k : BurnolL2))))

/-- The original K/FK feet consume the generated physical tail vector and actual G readback. -/
theorem actual_quarter_tail_K_prices :
 OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
   (burnolRadiusNormalizedUnitTail (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) q (by norm_num))=
 actualQuarterTailPairPrice observation nontrivial half ∧
 OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
   (burnolRadiusNormalizedUnitTail (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) q (by norm_num))=
 actualQuarterTailSiblingPrice observation nontrivial half := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let k:=burnolCompletedMellinRieszVector coordinate
 have first:=actual_physical_source_price k coordinate
 have second:=actual_physical_source_price (evenFaceFourierEquiv burnolUnscaledCommonGapRadius k) coordinate
 change inner ℂ (fourierL2 (k : BurnolL2)) (burnolRadiusNormalizedUnitTail coordinate q (by norm_num))=
   -(2:ℂ)*inner ℂ (evenFaceFourierEquiv burnolUnscaledCommonGapRadius k)
     (burnolCompletedMellinRieszVector (actualStarSource coordinate))+
   ((2:ℂ)*star (burnolMellinGapMoment (actualStarSource coordinate).value))*
     star (Paid.actualMean (fourierL2 (k : BurnolL2))) at second
 constructor
 · rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification,first,second]
   unfold actualQuarterTailPairPrice
   dsimp only
   simp only [star_add,star_mul,star_star]
   norm_num
   ring
 · rw [OriginalKPairedResponseGramAction.original_kernel_sibling_qualification,first,second]
   unfold actualQuarterTailSiblingPrice
   dsimp only
   ring


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQuarterTailPhysicalSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
