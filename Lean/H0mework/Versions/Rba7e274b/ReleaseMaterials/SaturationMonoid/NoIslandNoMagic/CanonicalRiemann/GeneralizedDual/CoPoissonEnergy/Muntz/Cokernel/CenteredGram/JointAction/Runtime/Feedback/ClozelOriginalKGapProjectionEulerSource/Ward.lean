import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapProjectionEulerSource.Strong
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

private theorem actual_source_R_Ward (coordinate : BurnolCompletedMellinCoordinate)
 (field velocity : BurnolL2)
 (source : HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift field) velocity 0)
 (input : BurnolL2) :
 let acted:=burnolDirectRightResolvent (coordinate.value/2) input
 inner ℂ velocity acted+inner ℂ field (-(coordinate.value-1/2) • acted-(2:ℂ) • input)=0 :=by
 dsimp only
 have right:1/4<(coordinate.value/2).re:=by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have reparam:HasDerivAt (fun time:ℝ=>-time/2) (-1/2:ℝ) 0:=by
  simpa only [Pi.neg_apply,neg_div,id_eq] using ((hasDerivAt_id (0:ℝ)).neg.div_const 2)
 have shifted:=source.scomp_of_eq (0:ℝ) reparam (by norm_num)
 have Rsource:=burnolDirectRightResolventOrbit_hasDerivAt (coordinate.value/2) right input
 have generated:=shifted.inner ℂ Rsource
 dsimp only [Function.comp_def] at generated
 simp only [neg_zero,zero_div,burnolMultiplicativeDilation_zero] at generated
 have fixed:(fun time:ℝ=>inner ℂ (burnolMultiplicativeDilation (-time/2) field)
  (burnolMultiplicativeDilation (-time/2) (burnolDirectRightResolvent (coordinate.value/2) input)))=
  fun _=>inner ℂ field (burnolDirectRightResolvent (coordinate.value/2) input) :=
 funext fun time=>(burnolMultiplicativeDilation (-time/2)).inner_map_map _ _
 rw [fixed] at generated
 have actual:=generated.unique (hasDerivAt_const (0:ℝ) (inner ℂ field
  (burnolDirectRightResolvent (coordinate.value/2) input)))
 rw [←algebraMap_smul ℂ (-1/2:ℝ)] at actual
 push_cast at actual
 simp only [inner_add_right,inner_smul_right,inner_smul_left,starRingEnd_apply,star_neg,star_div₀,star_one,star_ofNat] at actual
 simp only [inner_sub_right,inner_smul_right]
 linear_combination -(2:ℂ)*actual

theorem actual_gap_R_ward (coordinate : BurnolCompletedMellinCoordinate) (input : BurnolL2) :
 let acted:=burnolDirectRightResolvent (coordinate.value/2) input
 inner ℂ actualGapVelocity acted+
 inner ℂ actualGapCorrected (-(coordinate.value-1/2) • acted-(2:ℂ) • input)=0 :=
 actual_source_R_Ward coordinate _ _ actual_gap_source_strong input

theorem actual_fourier_gap_R_ward (coordinate : BurnolCompletedMellinCoordinate) (input : BurnolL2) :
 let acted:=burnolDirectRightResolvent (coordinate.value/2) input
 inner ℂ actualFourierGapVelocity acted+
 inner ℂ actualFourierGapCorrected (-(coordinate.value-1/2) • acted-(2:ℂ) • input)=0 :=
 actual_source_R_Ward coordinate _ _ actual_fourier_gap_source_strong input

/-- The actual G source produces a complete original R equation, without target price input. -/
theorem actual_gap_R_equation (coordinate : BurnolCompletedMellinCoordinate) (input : BurnolL2) :
 let acted:=burnolDirectRightResolvent (coordinate.value/2) input
 coordinate.value*inner ℂ (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2) acted=
 star actualGapA*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeU-OriginalRieszSource.Response.wholeV) acted+
 star actualGapBeta*inner ℂ (OriginalRieszSource.Response.wholeU-fourierL2 OriginalRieszSource.Response.wholeV) acted+
 coordinate.value*star actualGapA*inner ℂ Seed.seed acted+
 (1-coordinate.value)*star actualGapBeta*inner ℂ (fourierL2 Seed.seed) acted-
 (2:ℂ)*inner ℂ actualGapCorrected input :=by
 dsimp only
 have source:=actual_gap_R_ward coordinate input
 dsimp only at source
 unfold actualGapVelocity actualGapCorrected at source
 simp only [inner_add_left,inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right,
  starRingEnd_apply,star_neg,star_div₀,star_one,star_ofNat,star_mul] at source
 unfold actualGapCorrected
 simp only [inner_add_left,inner_sub_left,inner_smul_left,starRingEnd_apply]
 linear_combination -source

/-- Actual Fourier source velocity retains both original source columns and complete unit corrections. -/
theorem actual_fourier_gap_velocity_source :
 actualFourierGapVelocity=(1/2:ℂ) • fourierL2 (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2)-
 actualGapA • (OriginalRieszSource.Response.wholeU-fourierL2 OriginalRieszSource.Response.wholeV)-
 actualGapBeta • (fourierL2 OriginalRieszSource.Response.wholeU-OriginalRieszSource.Response.wholeV)-
 ((1/2:ℂ)*actualGapA) • fourierL2 Seed.seed-((1/2:ℂ)*actualGapBeta) • Seed.seed :=by
 unfold actualFourierGapVelocity actualGapVelocity
 simp only [map_add,map_sub,map_smul]
 rw [fourierL2_fourierL2,fourierL2_fourierL2,fourierL2_fourierL2,
  OriginalRieszSource.Response.wholeU_reflection,OriginalRieszSource.Response.wholeV_reflection,actual_seed_even]
 module

theorem actual_fourier_gap_corrected_source :
 actualFourierGapCorrected=fourierL2 (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2)-
 actualGapA • fourierL2 Seed.seed+actualGapBeta • Seed.seed :=by
 unfold actualFourierGapCorrected actualGapCorrected
 simp only [map_add,map_sub,map_smul]
 rw [fourierL2_fourierL2,actual_seed_even]

/-- The opposite source equation is generated from actual G Fourier action, with no free resonant price. -/
theorem actual_fourier_gap_R_equation (coordinate : BurnolCompletedMellinCoordinate) (input : BurnolL2) :
 let acted:=burnolDirectRightResolvent (coordinate.value/2) input
 (1-coordinate.value)*inner ℂ (fourierL2 (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2)) acted=
 star actualGapA*inner ℂ (OriginalRieszSource.Response.wholeU-fourierL2 OriginalRieszSource.Response.wholeV) acted+
 star actualGapBeta*inner ℂ (fourierL2 OriginalRieszSource.Response.wholeU-OriginalRieszSource.Response.wholeV) acted-
 (coordinate.value-1)*star actualGapA*inner ℂ (fourierL2 Seed.seed) acted+
 coordinate.value*star actualGapBeta*inner ℂ Seed.seed acted+
 (2:ℂ)*inner ℂ actualFourierGapCorrected input :=by
 dsimp only
 have source:=actual_fourier_gap_R_ward coordinate input
 dsimp only at source
 rw [actual_fourier_gap_velocity_source,actual_fourier_gap_corrected_source] at source
 simp only [inner_add_left,inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right,
  starRingEnd_apply,star_div₀,star_one,star_ofNat,star_mul] at source
 rw [actual_fourier_gap_corrected_source]
 simp only [inner_add_left,inner_sub_left,inner_smul_left,starRingEnd_apply]
 linear_combination source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
