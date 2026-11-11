import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelCompressedSourceAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelCompressedSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalRieszSource
local notation "F" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local instance effectComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem actual_physical_Fourier_cotest (test : BurnolPaAmbientCarrier) (source : BurnolL2) :
    inner ℂ (test : BurnolL2) (fourierL2 source) = inner ℂ (F test : BurnolL2) source := by
  have generated := fourierL2.inner_map_map (fourierL2 (test : BurnolL2)) source
  rw [fourierL2_fourierL2, (mem_evenL2ClosedFace_iff).mp test.property.2] at generated
  exact generated

theorem actual_physical_Fourier_dilation_cotest (test : BurnolPaAmbientCarrier)
    (source : BurnolL2) (t : ℝ) :
    inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation t (fourierL2 source)) =
      inner ℂ (F test : BurnolL2) (burnolMultiplicativeDilation (-t) source) := by
  have generated := fourierL2_burnolMultiplicativeDilation (-t) source
  simp only [neg_neg] at generated
  rw [←generated,actual_physical_Fourier_cotest]

theorem actual_compressed_Fourier_source_cotest (test : BurnolPaAmbientCarrier)
    (source : BurnolQuarterMeanZeroCarrier) (t : ℝ) (nonnegative : 0 ≤ t) :
    inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation (-t)
      (fourierL2 (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2)))) = 0 := by
  rw [actual_physical_Fourier_dilation_cotest,neg_neg]
  exact actual_compressed_meanZero_source_cotest (F test) source t nonnegative

def actualResponseVelocity (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Kernel.A coordinate • (fourierL2 Response.wholeU - Response.wholeV) +
    Kernel.beta coordinate • (Response.wholeU - fourierL2 Response.wholeV)

def actualContactVelocity (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(star coordinate.value-1/2) • (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
    ((1/2:ℂ)*Kernel.A coordinate) • OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed +
    ((1/2:ℂ)*Kernel.beta coordinate) • fourierL2 OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed

theorem actual_source_velocity_contact_inventory (coordinate : BurnolCompletedMellinCoordinate) :
    OriginalKBoundarySourceAction.Source.velocity coordinate = actualContactVelocity coordinate + actualResponseVelocity coordinate := by
  unfold OriginalKBoundarySourceAction.Source.velocity actualContactVelocity actualResponseVelocity
  module

/-- Positive source action annihilates only the compressed U/V legs and keeps both expanded Fourier-source legs. -/
theorem actual_positive_response_cotest (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolPaAmbientCarrier) (t : ℝ) (nonnegative : 0 ≤ t) :
    inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation t (actualResponseVelocity coordinate)) =
      Kernel.A coordinate * inner ℂ (F test : BurnolL2) (burnolMultiplicativeDilation (-t) Response.wholeU) -
      Kernel.beta coordinate * inner ℂ (F test : BurnolL2) (burnolMultiplicativeDilation (-t) Response.wholeV) := by
  unfold actualResponseVelocity
  simp only [map_add,map_smul,map_sub,inner_add_right,inner_smul_right,inner_sub_right]
  rw [actual_compressed_UV_source_cotests test t nonnegative |>.1,
    actual_compressed_UV_source_cotests test t nonnegative |>.2,
    actual_physical_Fourier_dilation_cotest,actual_physical_Fourier_dilation_cotest]
  ring

/-- Negative source action annihilates only the compressed Fourier legs and keeps the complete expanded U/V source fields. -/
theorem actual_negative_response_cotest (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolPaAmbientCarrier) (t : ℝ) (nonnegative : 0 ≤ t) :
    inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation (-t) (actualResponseVelocity coordinate)) =
      -Kernel.A coordinate * inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation (-t) Response.wholeV) +
      Kernel.beta coordinate * inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation (-t) Response.wholeU) := by
  unfold actualResponseVelocity
  simp only [map_add,map_smul,map_sub,inner_add_right,inner_smul_right,inner_sub_right]
  have u : inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation (-t) (fourierL2 Response.wholeU)) = 0 :=
    actual_compressed_Fourier_source_cotest test Response.u t nonnegative
  have v : inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation (-t) (fourierL2 Response.wholeV)) = 0 :=
    actual_compressed_Fourier_source_cotest test Response.v t nonnegative
  rw [u,v]
  ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelCompressedSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
