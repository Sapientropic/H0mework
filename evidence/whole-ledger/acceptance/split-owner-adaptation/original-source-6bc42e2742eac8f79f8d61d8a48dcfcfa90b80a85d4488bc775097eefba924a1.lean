import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapKernelGreenSource.Pair
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
local instance gapKernelEndpointComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "q" => (1/4:ℝ)
local notation "g" => Gap.actualGapResponse
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "u" => OriginalRieszSource.Response.u
local notation "v" => OriginalRieszSource.Response.v

elab "paidEtaPhaseInner" : term => do
 let head := ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Green.Eta".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
 let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszSourceGreen.phase_inner".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
 return Lean.mkConst full
elab "paidEtaConstantInner" : term => do
 let head := ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Green.Eta".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
 let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszSourceGreen.constant_inner".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
 return Lean.mkConst full
elab "paidKernelResponseRead" : term => do
 let head := ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Green.Assemble".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
 let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszSourceGreen.response_read".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
 return Lean.mkConst full

/-- The same endpoint source is consumed on the actual seed-response inverse, retaining its own mean and both ±q contacts. -/
theorem actual_gap_eta_endpoint_price :
 inner ℂ OriginalRieszSource.Response.eta g=(1/2:ℂ)*Gap.actualGapReturnEndpoint :=by
 let mean:=burnolQuarterMeanCoefficient (burnolTruncatedFourier (g:BurnolQuarterIntervalL2))
 have plus:OriginalRieszSource.Constructor.fourierRaw (g:BurnolQuarterIntervalL2) q=
  Gap.actualGapReturnEndpoint+mean :=by
  rw [OriginalRieszSource.Constructor.fourierRaw_state]
  change _=(_-mean)+mean
  ring
 have minus:OriginalRieszSource.Constructor.fourierRaw (g:BurnolQuarterIntervalL2) (-q)=
  Gap.actualGapReturnEndpoint+mean :=by
  have endpoints:=OriginalKGapProjectionEulerSource.actual_gap_return_endpoints
  change OriginalRieszSource.Constructor.fourierRaw (g:BurnolQuarterIntervalL2) (-q)-mean=
   OriginalRieszSource.Constructor.fourierRaw (g:BurnolQuarterIntervalL2) q-mean at endpoints
  linear_combination endpoints+plus
 have constant:inner ℂ (burnolTruncatedFourier (intervalConstant q)) (g:BurnolQuarterIntervalL2)=
  (1/2:ℂ)*mean :=by
  rw [OriginalRieszSourceGreen.quarter_fourier_pairing_of_reflection _ _ OriginalKGapProjectionEulerSource.actual_gap_response_even]
  exact paidEtaConstantInner _
 unfold OriginalRieszSource.Response.eta OriginalRieszSource.Constructor.endpointColumn
 rw [inner_add_left]
 simp only [OriginalRieszSource.Constructor.zeroMean,
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,inner_sub_left,inner_smul_left]
 rw [paidEtaPhaseInner,paidEtaPhaseInner,neg_neg,plus,minus,constant]
 norm_num [map_ofNat]
 ring

/-- The actual common inverse recovers both response feet from the same endpoint equation. -/
theorem actual_gap_inverse_endpoint_reads :
 inner ℂ u g-inner ℂ v (T g)=(1/2:ℂ)*Gap.actualGapReturnEndpoint ∧
 inner ℂ u (T g)=inner ℂ v g :=by
 have paired:=OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection v g
  OriginalKGapProjectionEulerSource.actual_gap_response_even
 have source:=OriginalRieszSource.Response.source_pair_equation
 constructor
 · rw [←paired,←inner_sub_left,source]
   exact actual_gap_eta_endpoint_price
 · exact (OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection u g
    OriginalKGapProjectionEulerSource.actual_gap_response_even).symm

/-- Existing actual kernel endpoint price is directly reused, with its original source owner and value. -/
theorem actual_original_kernel_endpoint_read (c : BurnolCompletedMellinCoordinate) :
 inner ℂ u (burnolRieszSingleFourierSource c)-
 inner ℂ v (T (burnolRieszSingleFourierSource c))=(1/2:ℂ)*burnolRieszReturnRaw c q :=
 paidKernelResponseRead c

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapKernelGreenSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
