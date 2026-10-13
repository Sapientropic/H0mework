import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteMResidualSource.Consumer
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
local instance gapKernelPairComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


namespace Gap
export OriginalKGapProjectionEulerSource (actualGapResponse actualGapResponseRaw actualGapResponseSlope actualGapResponseEuler actualGapEndpoint actualGapReturnRaw actualGapReturnEuler actualGapReturnEndpoint actualGapA actualGapBeta)
end Gap
local notation "q" => (1/4:ℝ)
local notation "b" => burnolRieszSingleFourierSource
local notation "T" => burnolMeanZeroTruncatedFourier

/-- The two real source legs consume the already-paid complete singular cotest Green law with their actual origin and endpoint qualifications. -/
theorem actual_kernel_gap_Euler_Green (c : BurnolCompletedMellinCoordinate) :
 inner ℂ (OriginalRieszSource.Euler.sourceEuler c) Gap.actualGapResponse+
 inner ℂ (b c) Gap.actualGapResponseEuler=
 (1/2:ℂ)*star (OriginalRieszSource.Kernel.beta c)*Gap.actualGapEndpoint :=by
 have source:=OriginalCommonInverseForcing.InverseEuler.source_interval_cotest_green c
  Gap.actualGapResponse Gap.actualGapResponseRaw Gap.actualGapResponseSlope
  OriginalKGapProjectionEulerSource.actual_gap_response_raw_continuous
  OriginalKGapProjectionEulerSource.actual_gap_response_slope_continuous
  OriginalKGapProjectionEulerSource.actual_gap_response_derivative
  OriginalKGapProjectionEulerSource.actual_gap_response_raw_read
 rw [OriginalKGapProjectionEulerSource.actual_gap_response_endpoints] at source
 change inner ℂ (OriginalRieszSource.Euler.sourceEuler c) Gap.actualGapResponse+
  inner ℂ (b c) Gap.actualGapResponseEuler=_ at source
 exact source.trans (by unfold Gap.actualGapEndpoint;push_cast;ring)

/-- The actual smooth return and the original gap return consume the paid return cotest law with both real endpoint contacts. -/
theorem actual_kernel_gap_return_Green (c : BurnolCompletedMellinCoordinate) :
 inner ℂ (OriginalRieszSource.Constructor.returnEuler c) (T Gap.actualGapResponse)+
 inner ℂ (T (b c)) Gap.actualGapReturnEuler=
 (1/2:ℂ)*star (burnolRieszReturnRaw c q)*Gap.actualGapReturnEndpoint :=by
 have source:=OriginalCommonInverseForcing.InverseEuler.return_interval_cotest_green c
  (T Gap.actualGapResponse) Gap.actualGapReturnRaw OriginalKGapProjectionEulerSource.actualGapReturnSlope
  (OriginalCommonInverseForcing.InverseEuler.meanZeroRaw_continuous Gap.actualGapResponse)
  (OriginalCommonInverseForcing.InverseEuler.state_derivative_continuous Gap.actualGapResponse)
  (OriginalCommonInverseForcing.InverseEuler.meanZeroRaw_hasDerivAt Gap.actualGapResponse)
  (burnolMeanZeroFourier_ae_raw Gap.actualGapResponse)
 rw [OriginalKGapProjectionEulerSource.actual_gap_return_endpoints] at source
 change inner ℂ (OriginalRieszSource.Constructor.returnEuler c) (T Gap.actualGapResponse)+
  inner ℂ (T (b c)) Gap.actualGapReturnEuler=_ at source
 exact source.trans (by unfold Gap.actualGapReturnEndpoint;push_cast;ring)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapKernelGreenSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
