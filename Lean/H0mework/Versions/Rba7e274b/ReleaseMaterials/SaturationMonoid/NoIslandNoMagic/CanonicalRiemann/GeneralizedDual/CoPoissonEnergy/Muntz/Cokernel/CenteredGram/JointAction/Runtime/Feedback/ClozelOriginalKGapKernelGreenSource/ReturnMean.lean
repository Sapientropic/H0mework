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
local instance gapKernelReturnMeanComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete



local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "b" => burnolRieszSingleFourierSource
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "u" => OriginalRieszSource.Response.u
local notation "v" => OriginalRieszSource.Response.v
local notation "g" => Gap.actualGapResponse
local notation "Sg" => OriginalKGapProjectionEulerSource.actualGapSource

/-- The actual returned source consumes its own ±q Fourier endpoints and same mean-zero face. -/
private theorem actual_even_eta_return_reader (state : BurnolQuarterMeanZeroCarrier)
 (even : reflectRestricted q (state:BurnolQuarterIntervalL2)=state)
 (endpoints : burnolMeanZeroFourierRaw state (-q)=burnolMeanZeroFourierRaw state q) :
 inner ℂ OriginalRieszSource.Response.eta state=(1/2:ℂ)*burnolMeanZeroFourierRaw state q :=by
 let mean:=burnolQuarterMeanCoefficient (burnolTruncatedFourier (state:BurnolQuarterIntervalL2))
 have plus:OriginalRieszSource.Constructor.fourierRaw (state:BurnolQuarterIntervalL2) q=
  burnolMeanZeroFourierRaw state q+mean :=by
  rw [OriginalRieszSource.Constructor.fourierRaw_state]
  change _=(_-mean)+mean
  ring
 have minus:OriginalRieszSource.Constructor.fourierRaw (state:BurnolQuarterIntervalL2) (-q)=
  burnolMeanZeroFourierRaw state q+mean :=by
  rw [OriginalRieszSource.Constructor.fourierRaw_state]
  change _-mean=(_-mean) at endpoints
  rw [OriginalRieszSource.Constructor.fourierRaw_state] at plus
  linear_combination endpoints+plus
 have constant:inner ℂ (burnolTruncatedFourier (intervalConstant q)) (state:BurnolQuarterIntervalL2)=
  (1/2:ℂ)*mean :=by
  rw [OriginalRieszSourceGreen.quarter_fourier_pairing_of_reflection _ _ even]
  exact paidEtaConstantInner _
 unfold OriginalRieszSource.Response.eta OriginalRieszSource.Constructor.endpointColumn
 rw [inner_add_left]
 simp only [OriginalRieszSource.Constructor.zeroMean,
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,inner_sub_left,inner_smul_left]
 rw [paidEtaPhaseInner,paidEtaPhaseInner,neg_neg,plus,minus,constant]
 norm_num [map_ofNat]
 ring

/-- The same g inverse is consumed on its actual Fourier forcing, before any target Fourier mean is read. -/
theorem actual_gap_source_inverse_reads :
 inner ℂ u Sg=(1/2:ℂ)*Gap.actualGapReturnEndpoint ∧
 inner ℂ v Sg=(1/2:ℂ)*(Gap.actualGapEndpoint-OriginalKGapProjectionEulerSource.actualGapSourceRaw q) :=by
 have pairU:inner ℂ u (T (T g))=inner ℂ (T (T u)) g :=by
  calc
   _=inner ℂ (T u) (T g) :=(OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection u (T g)
    OriginalKGapProjectionEulerSource.actual_gap_return_even).symm
   _=_ :=(OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection (T u) g
    OriginalKGapProjectionEulerSource.actual_gap_response_even).symm
 have uRead:=congrArg (fun field:BurnolQuarterMeanZeroCarrier=>inner ℂ u field)
  OriginalKGapProjectionEulerSource.actual_gap_response_equation
 change inner ℂ u (g-T (T g))=inner ℂ u Sg at uRead
 rw [inner_sub_right,pairU,←inner_sub_left] at uRead
 have uEq:u-T (T u)=OriginalRieszSource.Response.eta:=OriginalRieszSource.Response.u_equation
 rw [uEq,actual_gap_eta_endpoint_price] at uRead
 have vRead:inner ℂ v Sg=inner ℂ u (T Sg) :=
  OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection u Sg
   (burnolAmbientMeanZeroFourier_reflection_fixed OriginalKConstantContactSourceAction.ConstantSource.seed)
 have gapEq:g-T (T g)=Sg:=OriginalKGapProjectionEulerSource.actual_gap_response_equation
 have TgRead:=congrArg T gapEq
 rw [map_sub] at TgRead
 have pairUTg:inner ℂ u (T (T (T g)))=inner ℂ (T (T u)) (T g) :=by
  have twiceEven:reflectRestricted q (T (T g):BurnolQuarterIntervalL2)=T (T g) :=by
   have actualReflection:=sourceMeanZeroFourier_reflect (T g)
   have own:sourceMeanZeroReflection (T g)=T g:=Subtype.ext OriginalKGapProjectionEulerSource.actual_gap_return_even
   rw [own] at actualReflection
   exact congrArg (fun x:BurnolQuarterMeanZeroCarrier=>(x:BurnolQuarterIntervalL2)) actualReflection.symm
  calc
   _=inner ℂ (T u) (T (T g)) :=(OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection u (T (T g)) twiceEven).symm
   _=_ :=(OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection (T u) (T g)
    OriginalKGapProjectionEulerSource.actual_gap_return_even).symm
 rw [vRead,←TgRead,inner_sub_right,pairUTg,←inner_sub_left,uEq]
 have returnRead:inner ℂ OriginalRieszSource.Response.eta (T g)=
  (1/2:ℂ)*burnolMeanZeroFourierRaw (T g) q :=by
  apply actual_even_eta_return_reader (T g) OriginalKGapProjectionEulerSource.actual_gap_return_even
  have parity:=paidFiniteRawEndpoints (T (T g)) (burnolMeanZeroFourierRaw (T g))
   (OriginalCommonInverseForcing.InverseEuler.meanZeroRaw_continuous (T g))
   (burnolMeanZeroFourier_ae_raw (T g))
  apply parity
  have actualReflection:=sourceMeanZeroFourier_reflect (T g)
  have own:sourceMeanZeroReflection (T g)=T g:=Subtype.ext OriginalKGapProjectionEulerSource.actual_gap_return_even
  rw [own] at actualReflection
  exact congrArg (fun x:BurnolQuarterMeanZeroCarrier=>(x:BurnolQuarterIntervalL2)) actualReflection.symm
 have fieldRead:burnolMeanZeroFourierRaw (T g) q=Gap.actualGapEndpoint-OriginalKGapProjectionEulerSource.actualGapSourceRaw q :=by
  unfold Gap.actualGapEndpoint OriginalKGapProjectionEulerSource.actualGapResponseRaw
  simp only [Pi.add_apply]
  ring
 rw [returnRead,fieldRead]
 exact ⟨uRead.symm,rfl⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapKernelGreenSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
