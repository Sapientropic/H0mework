import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapKernelGreenSource.ReturnMean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapKernelGreenSource.Reality
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
local instance gapKernelFourierSourceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "q" => (1/4:ℝ)
local notation "b" => burnolRieszSingleFourierSource
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "Sg" => OriginalKGapProjectionEulerSource.actualGapSource

elab "paidOwnEtaReturnReader" : term => do
 let head := ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapKernelGreenSource.ReturnMean".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
 let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapKernelGreenSource.actual_even_eta_return_reader".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
 return Lean.mkConst full

/-- The actual returned b source consumes the original eta endpoint reader on its genuine Fourier return and own source endpoint. -/
theorem actual_kernel_return_eta_endpoint_price (c : BurnolCompletedMellinCoordinate) :
 inner ℂ OriginalRieszSource.Response.eta (T (b c))=
 (1/2:ℂ)*(OriginalRieszSource.Kernel.beta c-burnolRieszFourierForcingRaw c q) :=by
 have even:reflectRestricted q (T (T (b c)):BurnolQuarterIntervalL2)=T (T (b c)) :=by
  have own:sourceMeanZeroReflection (T (b c))=T (b c):=
   Subtype.ext (burnolRieszSingleFourierReturn_reflection_fixed c)
  have actual:=sourceMeanZeroFourier_reflect (T (b c))
  rw [own] at actual
  exact congrArg (fun x:BurnolQuarterMeanZeroCarrier=>(x:BurnolQuarterIntervalL2)) actual.symm
 have endpoints:=paidFiniteRawEndpoints (T (T (b c))) (burnolMeanZeroFourierRaw (T (b c)))
  (OriginalCommonInverseForcing.InverseEuler.meanZeroRaw_continuous (T (b c)))
  (burnolMeanZeroFourier_ae_raw (T (b c))) even
 have read:=paidOwnEtaReturnReader (T (b c)) (burnolRieszSingleFourierReturn_reflection_fixed c) endpoints
 have actualReturn:burnolMeanZeroFourierRaw (T (b c)) q=OriginalRieszSource.Constructor.secondReturnRaw c q :=rfl

 rw [actualReturn] at read
 have raw:OriginalRieszSource.Constructor.secondReturnRaw c q=
  OriginalRieszSource.Kernel.beta c-burnolRieszFourierForcingRaw c q :=by
  change _=(burnolRieszFourierForcingRaw c q+OriginalRieszSource.Constructor.secondReturnRaw c q)-burnolRieszFourierForcingRaw c q
  ring
 rw [raw] at read
 exact read

/-- The actual returned kernel is paired with the original Fourier-unit forcing through its already-generated Euler equation. -/
theorem actual_kernel_return_gap_source_Green (c : BurnolCompletedMellinCoordinate) :
 (1-c.value)*inner ℂ (T (b c)) Sg=
 (1/2:ℂ)*(star (OriginalRieszSource.Kernel.A c)*Gap.actualGapEndpoint-
  star (OriginalRieszSource.Kernel.beta c)*(1+Gap.actualGapReturnEndpoint))+
 (1/2:ℂ)*(c.value-1)*star (OriginalRieszSource.Translator.ForcingMeanZero.mean c) :=by
 have source:=OriginalCommonInverseForcing.InverseEuler.return_interval_cotest_green c Sg
  OriginalKGapProjectionEulerSource.actualGapSourceRaw OriginalKGapProjectionEulerSource.actualGapSourceSlope
  OriginalKGapProjectionEulerSource.actual_gap_source_continuous
  OriginalKGapProjectionEulerSource.actual_gap_source_slope_continuous
  OriginalKGapProjectionEulerSource.actual_gap_source_derivative
  OriginalKGapProjectionEulerSource.actual_gap_source_read
 have endpoints:OriginalKGapProjectionEulerSource.actualGapSourceRaw (-q)=OriginalKGapProjectionEulerSource.actualGapSourceRaw q :=by
  apply paidFiniteRawEndpoints Sg OriginalKGapProjectionEulerSource.actualGapSourceRaw
   OriginalKGapProjectionEulerSource.actual_gap_source_continuous OriginalKGapProjectionEulerSource.actual_gap_source_read
  exact burnolAmbientMeanZeroFourier_reflection_fixed OriginalKConstantContactSourceAction.ConstantSource.seed
 rw [endpoints] at source
 change inner ℂ (OriginalRieszSource.Constructor.returnEuler c) Sg+
  inner ℂ (T (b c)) OriginalKGapProjectionEulerSource.actualGapSourceEuler=_ at source
 rw [OriginalRieszSource.Euler.returnEuler_eq,OriginalKGapProjectionEulerSource.actual_gap_source_Euler] at source
 simp only [inner_add_left,inner_sub_left,inner_smul_left,inner_add_right,inner_smul_right,
  starRingEnd_apply,star_neg,star_sub,star_div₀,star_one,star_ofNat,star_star] at source
 have actual:=actual_gap_source_inverse_reads
 rw [actual.1,actual.2,actual_gap_source_endpoint_mean] at source
 have eta:=congrArg (starRingEnd ℂ) (actual_kernel_return_eta_endpoint_price c)
 simp only [map_mul,map_div₀,map_one,map_ofNat,map_sub,starRingEnd_apply] at eta
 have etaRead : inner ℂ (T (b c)) OriginalRieszSource.Response.eta=
  (1/2:ℂ)*(star (OriginalRieszSource.Kernel.beta c)-star (burnolRieszFourierForcingRaw c q)) :=
  ((inner_conj_symm (T (b c)) OriginalRieszSource.Response.eta).symm).trans eta
 rw [etaRead] at source
 push_cast at source
 have forcing:=congrArg (starRingEnd ℂ) (OriginalRieszSource.Translator.ForcingMeanZero.forcing_mean_boundary c)
 simp only [map_add,map_mul,map_sub,map_one,starRingEnd_apply,star_star] at forcing
 have endpoint:star (OriginalRieszSource.Kernel.A c)=c.value*star (OriginalRieszSource.GapEuler.gapMean q c)+star (burnolRieszReturnRaw c q) :=by
  simp only [OriginalRieszSource.Kernel.A,star_add,star_mul,star_star]
  ring
 unfold OriginalRieszSource.Translator.ForcingWhole.coefficient at forcing
 simp only [star_mul,star_star] at forcing
 rw [actual_original_edge_mean_real] at forcing
 linear_combination source+(1/2:ℂ)*forcing-
  (1/2:ℂ)*OriginalRieszSource.Translator.ForcingMeanZero.edgeMean*endpoint

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapKernelGreenSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
