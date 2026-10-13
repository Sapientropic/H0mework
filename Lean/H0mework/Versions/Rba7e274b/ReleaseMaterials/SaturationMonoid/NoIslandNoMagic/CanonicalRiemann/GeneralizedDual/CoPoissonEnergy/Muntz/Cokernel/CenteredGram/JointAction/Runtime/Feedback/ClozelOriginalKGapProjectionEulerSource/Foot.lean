import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapProjectionEulerSource.Ward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
open Complex MeasureTheory Set Filter FourierTransform SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

local instance gapFootPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The actual physical Fourier input is read by the same unitary source, without a new physical qualification. -/
theorem actual_source_fourier_input (source : BurnolL2) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (fourierL2 source) (physical:BurnolL2)=
 inner ℂ source (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical:BurnolL2) :=by
 have twice:fourierL2 (fourierL2 (physical:BurnolL2))=(physical:BurnolL2):=by
  rw [fourierL2_fourierL2]
  exact mem_evenL2ClosedFace_iff.mp physical.property.2
 have sourceRead:=fourierL2.inner_map_map source (fourierL2 (physical:BurnolL2))
 rw [twice] at sourceRead
 exact sourceRead

/-- Own mean-zero quarter columns are read only after the actual physical R source field is generated. -/
theorem actual_source_quarter_R_zero (coordinate : BurnolCompletedMellinCoordinate)
 (column : BurnolQuarterMeanZeroCarrier) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (burnolQuarterZeroExtension (column:BurnolQuarterIntervalL2))
  (burnolDirectRightResolvent (coordinate.value/2) (physical:BurnolL2))=0 :=by
 have right:1/4<(coordinate.value/2).re:=by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have source:=OriginalKGapMeanRSourceAction.original_R_quarter_source_action (coordinate.value/2) right physical
 have read:=(burnolRadiusRestriction q).adjoint_inner_left
  (burnolDirectRightResolvent (coordinate.value/2) (physical:BurnolL2)) (column:BurnolQuarterIntervalL2)
 change inner ℂ (burnolQuarterZeroExtension (column:BurnolQuarterIntervalL2))
  (burnolDirectRightResolvent (coordinate.value/2) (physical:BurnolL2))=
  inner ℂ (column:BurnolQuarterIntervalL2) (burnolRadiusRestriction q
   (burnolDirectRightResolvent (coordinate.value/2) (physical:BurnolL2))) at read
 rw [source,inner_smul_right] at read
 have zero:inner ℂ (column:BurnolQuarterIntervalL2) (intervalConstant q)=0 :=by
  rw [inner_eq_zero_symm]
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mp column.property
 rw [zero,mul_zero] at read
 exact read

/-- The original seed response is computed from the actual quarter field and its paid half unit. -/
theorem actual_seed_R_physical_price (coordinate : BurnolCompletedMellinCoordinate)
 (physical : BurnolPaAmbientCarrier) :
 inner ℂ Seed.seed (burnolDirectRightResolvent (coordinate.value/2) (physical:BurnolL2))=
 -Paid.actualMean (physical:BurnolL2)/coordinate.value :=by
 have right:1/4<(coordinate.value/2).re:=by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have source:=OriginalKGapMeanRSourceAction.original_R_quarter_source_action (coordinate.value/2) right physical
 have read:=(burnolRadiusRestriction q).adjoint_inner_left
  (burnolDirectRightResolvent (coordinate.value/2) (physical:BurnolL2)) (intervalConstant q)
 change inner ℂ Seed.seed (burnolDirectRightResolvent (coordinate.value/2) (physical:BurnolL2))=
  inner ℂ (intervalConstant q) (burnolRadiusRestriction q
   (burnolDirectRightResolvent (coordinate.value/2) (physical:BurnolL2))) at read
 rw [source,inner_smul_right,inner_self_eq_norm_sq_to_K] at read
 have normsource:((‖intervalConstant q‖:ℝ):ℂ)^2=(1/2:ℂ):=by
  have native:=burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)
  norm_num at native
  exact native
 change inner ℂ Seed.seed (burnolDirectRightResolvent (coordinate.value/2) (physical:BurnolL2))=
  (-Paid.actualMean (physical:BurnolL2)/(coordinate.value/2))*(((‖intervalConstant q‖:ℝ):ℂ)^2) at read
 rw [normsource] at read
 rw [read]
 have qualified:coordinate.value≠0:=by
  intro zero
  have real:=congrArg Complex.re zero
  simp only [Complex.zero_re] at real
  linarith [coordinate.rightHalf]
 field_simp [qualified]

theorem actual_gap_physical_input_price (physical : BurnolPaAmbientCarrier) :
 inner ℂ (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2) (physical:BurnolL2)=Paid.actualMean (physical:BurnolL2) :=
 OriginalRieszFiniteSynthesis.gapMeanVector_readback physical

def actualGapCorrectedInputPrice (physical : BurnolPaAmbientCarrier) : ℂ:=
 (1-star actualGapA/2)*Paid.actualMean (physical:BurnolL2)+
 (star actualGapBeta/2)*Paid.actualMean (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical:BurnolL2)
def actualFourierGapCorrectedInputPrice (physical : BurnolPaAmbientCarrier) : ℂ:=
 (1-star actualGapA/2)*Paid.actualMean (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical:BurnolL2)+
 (star actualGapBeta/2)*Paid.actualMean (physical:BurnolL2)

theorem actual_gap_corrected_input (physical : BurnolPaAmbientCarrier) :
 inner ℂ actualGapCorrected (physical:BurnolL2)=actualGapCorrectedInputPrice physical :=by
 unfold actualGapCorrected
 rw [inner_add_left,inner_sub_left,inner_smul_left,inner_smul_left,
  actual_gap_physical_input_price,actual_source_fourier_input,
  OriginalKConstantContactSourceAction.actual_constant_seed_input_price,
  OriginalKConstantContactSourceAction.actual_constant_seed_input_price]
 unfold actualGapCorrectedInputPrice
 simp only [starRingEnd_apply]
 ring

theorem actual_fourier_gap_corrected_input (physical : BurnolPaAmbientCarrier) :
 inner ℂ actualFourierGapCorrected (physical:BurnolL2)=actualFourierGapCorrectedInputPrice physical :=by
 rw [actual_fourier_gap_corrected_source,inner_add_left,inner_sub_left,
  inner_smul_left,inner_smul_left,actual_source_fourier_input,actual_source_fourier_input,
  actual_gap_physical_input_price,OriginalKConstantContactSourceAction.actual_constant_seed_input_price,
  OriginalKConstantContactSourceAction.actual_constant_seed_input_price]
 unfold actualFourierGapCorrectedInputPrice
 simp only [starRingEnd_apply]
 ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
