import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapKernelGreenSource.Boundary
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
local instance gapKernelSourceRealityComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


open scoped FourierTransform ComplexConjugate
local notation "q" => (1/4:ℝ)

/-- The original Fourier character has its actual source conjugate parity. -/
private theorem actual_source_phase_star (frequency x : ℝ) :
 star (OriginalRieszSource.Constructor.phase frequency x)=OriginalRieszSource.Constructor.phase frequency (-x) :=by
 unfold OriginalRieszSource.Constructor.phase
 rw [Complex.star_def,←Circle.coe_inv_eq_conj,←AddChar.map_neg_eq_inv]
 congr 1
 ring

/-- The literal real even constant source generates a real Fourier value; no kernel target mean is assumed. -/
theorem actual_original_constant_Fourier_real (frequency : ℝ) :
 star (OriginalRieszSource.Constructor.fourierRaw (fun _:ℝ=>(1:ℂ)) frequency)=
  OriginalRieszSource.Constructor.fourierRaw (fun _:ℝ=>(1:ℂ)) frequency :=by
 rw [OriginalRieszSource.Constructor.fourierRaw_integral]
 simp only [mul_one]
 change conj (∫ x:ℝ in (-q)..q,OriginalRieszSource.Constructor.phase frequency x)=_
 rw [←intervalIntegral.intervalIntegral_conj]
 change (∫ x:ℝ in (-q)..q,star (OriginalRieszSource.Constructor.phase frequency x))=_
 simp_rw [actual_source_phase_star]
 rw [intervalIntegral.integral_comp_neg]
 simp only [neg_neg]

/-- The actual Fourier-unit source quarter mean is real by its source adjoint pairing. -/
theorem actual_original_constant_Fourier_mean_real :
 star OriginalKGapProjectionEulerSource.actualGapSourceMean=OriginalKGapProjectionEulerSource.actualGapSourceMean :=by
 have paired:=OriginalRieszSourceGreen.quarter_fourier_pairing_of_reflection
  (intervalConstant q) (intervalConstant q) (reflectRestricted_intervalConstant q)
 have actual:star (inner ℂ (intervalConstant q) (burnolTruncatedFourier (intervalConstant q)))=
  inner ℂ (intervalConstant q) (burnolTruncatedFourier (intervalConstant q)) :=
  (inner_conj_symm (burnolTruncatedFourier (intervalConstant q)) (intervalConstant q)).trans paired
 unfold OriginalKGapProjectionEulerSource.actualGapSourceMean burnolQuarterMeanCoefficient
 rw [star_div₀,actual]
 simp only [Complex.star_def,Complex.conj_ofReal]

/-- The actual source endpoint and its paid full Euler mean generate the edge-mean reality qualification. -/
theorem actual_original_edge_mean_real :
 star OriginalRieszSource.Translator.ForcingMeanZero.edgeMean=OriginalRieszSource.Translator.ForcingMeanZero.edgeMean :=by
 rw [←actual_gap_source_endpoint_mean]
 unfold OriginalKGapProjectionEulerSource.actualGapSourceRaw
 simp only [Pi.sub_apply,star_sub]
 rw [actual_original_constant_Fourier_real,actual_original_constant_Fourier_mean_real]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapKernelGreenSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
