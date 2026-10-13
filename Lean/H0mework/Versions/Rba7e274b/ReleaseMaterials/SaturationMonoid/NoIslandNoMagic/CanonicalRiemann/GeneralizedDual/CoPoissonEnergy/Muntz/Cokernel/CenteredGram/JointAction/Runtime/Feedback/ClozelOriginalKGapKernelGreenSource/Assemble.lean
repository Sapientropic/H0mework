import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapKernelGreenSource.Endpoint
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
local instance gapKernelAssembleComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "q" => (1/4:ℝ)
local notation "b" => burnolRieszSingleFourierSource
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "g" => Gap.actualGapResponse
local notation "u" => OriginalRieszSource.Response.u
local notation "v" => OriginalRieszSource.Response.v

/-- The original kernel and the actual seed-response Green equations consume their common inverse endpoint receipts before yielding the weighted correction Gram. -/
theorem actual_gap_kernel_correction_Green (c : BurnolCompletedMellinCoordinate) :
 c.value*(inner ℂ (b c) g-inner ℂ (T (b c)) (T g))=
 (1/4:ℂ)*(star (OriginalRieszSource.Kernel.beta c)*Gap.actualGapBeta-
  star (OriginalRieszSource.Kernel.A c)*Gap.actualGapA)+
 (1/2:ℂ)*c.value*star (OriginalRieszSource.GapEuler.gapMean q c) :=by
 have bGreen:=actual_kernel_gap_Euler_Green c
 have rGreen:=actual_kernel_gap_return_Green c
 have gapRead:=actual_gap_inverse_endpoint_reads
 have kernelRead:=congrArg (starRingEnd ℂ) (actual_original_kernel_endpoint_read c)
 have kernelCross:=congrArg (starRingEnd ℂ) (OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection u (b c)
  (burnolRieszSingleFourierSource_reflection_fixed c)).symm
 simp only [map_sub,map_mul,map_div₀,map_one,map_ofNat,inner_conj_symm] at kernelRead
 simp only [starRingEnd_apply] at kernelRead
 simp only [inner_conj_symm] at kernelCross
 change inner ℂ (T (b c)) u=inner ℂ (b c) v at kernelCross
 rw [OriginalRieszSource.Euler.sourceEuler_eq,OriginalKGapProjectionEulerSource.actual_gap_response_Euler_source] at bGreen
 rw [OriginalRieszSource.Euler.returnEuler_eq,OriginalKGapProjectionEulerSource.actual_gap_return_Euler_source] at rGreen
 simp only [inner_add_left,inner_sub_left,inner_smul_left,inner_add_right,inner_sub_right,
  inner_smul_right,starRingEnd_apply,star_sub,star_neg,star_div₀,star_one,star_ofNat,star_star] at bGreen rGreen
 unfold Gap.actualGapA Gap.actualGapBeta
 have endpoint:star (OriginalRieszSource.Kernel.A c)=c.value*star (OriginalRieszSource.GapEuler.gapMean q c)+star (burnolRieszReturnRaw c q) :=by
  simp only [OriginalRieszSource.Kernel.A,star_add,star_mul,star_star]
  ring
 linear_combination bGreen+rGreen-star (OriginalRieszSource.Kernel.A c)*gapRead.1+
  -star (OriginalRieszSource.Kernel.beta c)*gapRead.2-
  (1+Gap.actualGapReturnEndpoint)*kernelRead-Gap.actualGapEndpoint*kernelCross+(1/2:ℂ)*endpoint

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapKernelGreenSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
