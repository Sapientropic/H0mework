import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapProjectionEulerSource.ResponseEuler
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

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

namespace WholePaid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszSource.Euler (smoothEuler_mean even_extension_euler)
end WholePaid
local notation "T" => burnolMeanZeroTruncatedFourier

def actualGapA : ℂ:=(2:ℂ)*(1+actualGapReturnEndpoint)
def actualGapBeta : ℂ:=(2:ℂ)*actualGapEndpoint

/-- The full return Euler action is generated from the same seed-response action and source endpoints. -/
theorem actual_gap_return_Euler_source :
 actualGapReturnEuler=-(1/2:ℂ) • (T actualGapResponse)+
 actualGapEndpoint • OriginalRieszSource.Response.u-
 (1+actualGapReturnEndpoint) • OriginalRieszSource.Response.v :=by
 have source:=actual_gap_response_ward
 have endpoint:EulerPaid.endpointReaction actualGapResponseRaw=
  actualGapEndpoint • OriginalRieszSource.Response.eta:=by
  unfold EulerPaid.endpointReaction
  rw [actual_gap_response_endpoints,←smul_add]
  rfl
 rw [endpoint,actual_gap_response_Euler_source,map_sub,map_add,map_smul,map_smul,map_smul] at source
 change actualGapReturnEuler+((1/2:ℂ) • T actualGapResponse+
  (1+actualGapReturnEndpoint) • OriginalRieszSource.Response.v-
  actualGapEndpoint • T OriginalRieszSource.Response.v)=actualGapEndpoint • OriginalRieszSource.Response.eta at source
 have eta:=OriginalRieszSource.Response.source_pair_equation
 change OriginalRieszSource.Response.u-T OriginalRieszSource.Response.v=OriginalRieszSource.Response.eta at eta
 linear_combination (norm:=module) source-actualGapEndpoint • eta

/-- Whole response Euler carries its original source contact; constants are removed only by the paid mean-zero face. -/
theorem actual_gap_response_whole_Euler :
 OriginalRieszSource.GapEuler.euler
  (burnolQuarterZeroExtension (actualGapResponse:BurnolQuarterIntervalL2):TemperedDistribution ℝ ℂ)=
 (burnolQuarterZeroExtension (actualGapResponseEuler:BurnolQuarterIntervalL2):TemperedDistribution ℝ ℂ)-
 actualGapEndpoint • OriginalRieszSource.GapEuler.edge q :=by
 exact WholePaid.even_extension_euler _ _ _ actual_gap_response_raw_read
  actual_gap_response_raw_continuous actual_gap_response_slope_continuous actual_gap_response_derivative
  (WholePaid.smoothEuler_mean _ _ _ actual_gap_response_raw_read actual_gap_response_raw_continuous
   actual_gap_response_slope_continuous actual_gap_response_derivative) actual_gap_response_endpoints

theorem actual_gap_return_whole_Euler :
 OriginalRieszSource.GapEuler.euler
  (burnolQuarterZeroExtension (T actualGapResponse:BurnolQuarterIntervalL2):TemperedDistribution ℝ ℂ)=
 (burnolQuarterZeroExtension (actualGapReturnEuler:BurnolQuarterIntervalL2):TemperedDistribution ℝ ℂ)-
 actualGapReturnEndpoint • OriginalRieszSource.GapEuler.edge q :=by
 exact WholePaid.even_extension_euler _ _ _ (burnolMeanZeroFourier_ae_raw actualGapResponse)
  (EulerPaid.meanZeroRaw_continuous _) (EulerPaid.state_derivative_continuous _)
  (EulerPaid.meanZeroRaw_hasDerivAt _)
  (WholePaid.smoothEuler_mean _ _ _ (burnolMeanZeroFourier_ae_raw actualGapResponse)
   (EulerPaid.meanZeroRaw_continuous _) (EulerPaid.state_derivative_continuous _)
   (EulerPaid.meanZeroRaw_hasDerivAt _)) actual_gap_return_endpoints

/-- The actual physical G whole field is computed before price read, preserving both distribution contacts. -/
theorem actual_gap_mean_Euler :
 OriginalRieszSource.GapEuler.euler ((OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2):TemperedDistribution ℝ ℂ)=
 -(1/2:ℂ) • ((OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2):TemperedDistribution ℝ ℂ)+
 actualGapA • OriginalRieszSource.Response.Psi+
 actualGapBeta • (fourierCLM ℂ (TemperedDistribution ℝ ℂ)) OriginalRieszSource.Response.Psi :=by
 have unit:=actualConstantEulerSource
 have whole:=actual_gap_mean_whole_source
 have first:=actual_gap_return_whole_Euler
 have second:=actual_gap_response_whole_Euler
 have Fourier: (fourierCLM ℂ (TemperedDistribution ℝ ℂ))
  (burnolQuarterZeroExtension (actualGapResponse:BurnolQuarterIntervalL2):TemperedDistribution ℝ ℂ)=
  (fourierL2 (burnolQuarterZeroExtension (actualGapResponse:BurnolQuarterIntervalL2)):TemperedDistribution ℝ ℂ):=
  Lp.fourier_toTemperedDistribution_eq _
 change OriginalRieszSource.GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
  (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2))=_
 rw [whole]
 unfold actualGapWhole
 simp only [map_smul,map_add,map_sub,Lp.toTemperedDistributionCLM_apply]
 have anti:OriginalRieszSource.GapEuler.euler ((fourierCLM ℂ (TemperedDistribution ℝ ℂ))
   (burnolQuarterZeroExtension (actualGapResponse:BurnolQuarterIntervalL2):TemperedDistribution ℝ ℂ))=
   -(fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (OriginalRieszSource.GapEuler.euler
    (burnolQuarterZeroExtension (actualGapResponse:BurnolQuarterIntervalL2):TemperedDistribution ℝ ℂ)):=
  OriginalRieszSource.GapEuler.euler_fourier _
 rw [unit,first,←Fourier,anti,second]
 simp only [map_sub,map_smul]
 have firstRead:=congrArg OriginalKResponseCofinalSourceAction.actualWholeRead actual_gap_return_Euler_source
 have secondRead:=congrArg OriginalKResponseCofinalSourceAction.actualWholeRead actual_gap_response_Euler_source
 simp only [map_sub,map_add,map_smul] at firstRead secondRead
 change burnolQuarterZeroExtension (actualGapReturnEuler:BurnolQuarterIntervalL2)=
  -(1/2:ℂ) • burnolQuarterZeroExtension (T actualGapResponse:BurnolQuarterIntervalL2)+
  actualGapEndpoint • OriginalRieszSource.Response.wholeU-
  (1+actualGapReturnEndpoint) • OriginalRieszSource.Response.wholeV at firstRead
 change burnolQuarterZeroExtension (actualGapResponseEuler:BurnolQuarterIntervalL2)=
  (1/2:ℂ) • burnolQuarterZeroExtension (actualGapResponse:BurnolQuarterIntervalL2)+
  (1+actualGapReturnEndpoint) • OriginalRieszSource.Response.wholeU-
  actualGapEndpoint • OriginalRieszSource.Response.wholeV at secondRead
 have firstDistr:=congrArg (Lp.toTemperedDistributionCLM ℂ volume 2) firstRead
 have secondDistr:=congrArg (Lp.toTemperedDistributionCLM ℂ volume 2) secondRead
 simp only [map_sub,map_add,map_smul,Lp.toTemperedDistributionCLM_apply] at firstDistr secondDistr
 rw [firstDistr,secondDistr]
 unfold actualGapA actualGapBeta
 have PsiRead:(fourierCLM ℂ (TemperedDistribution ℝ ℂ)) OriginalRieszSource.Response.Psi=
  (OriginalRieszSource.Response.wholeU:TemperedDistribution ℝ ℂ)-
  (fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (OriginalRieszSource.Response.wholeV:TemperedDistribution ℝ ℂ)-
  (fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (OriginalRieszSource.GapEuler.edge q):=OriginalRieszSource.Response.Psi_fourier
 rw [PsiRead]
 have rawPsi:OriginalRieszSource.Response.Psi=
  (fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (OriginalRieszSource.Response.wholeU:TemperedDistribution ℝ ℂ)-
  (OriginalRieszSource.Response.wholeV:TemperedDistribution ℝ ℂ)-OriginalRieszSource.GapEuler.edge q:=rfl
 rw [rawPsi]
 have FU: (fourierCLM ℂ (TemperedDistribution ℝ ℂ))
  (OriginalRieszSource.Response.wholeU:TemperedDistribution ℝ ℂ)=
  (fourierL2 OriginalRieszSource.Response.wholeU:TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
 have FV: (fourierCLM ℂ (TemperedDistribution ℝ ℂ))
  (OriginalRieszSource.Response.wholeV:TemperedDistribution ℝ ℂ)=
  (fourierL2 OriginalRieszSource.Response.wholeV:TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
 simp only [map_sub,map_add,map_smul]
 rw [FU,FV,Fourier]
 have rawRead:(Lp.toTemperedDistributionCLM ℂ volume 2)
   ((2:ℂ) • (Seed.seed+burnolQuarterZeroExtension (T actualGapResponse:BurnolQuarterIntervalL2)-
    fourierL2 (burnolQuarterZeroExtension (actualGapResponse:BurnolQuarterIntervalL2)) ))=
   (2:ℂ) • ((Seed.seed:TemperedDistribution ℝ ℂ)+
    (burnolQuarterZeroExtension (T actualGapResponse:BurnolQuarterIntervalL2):TemperedDistribution ℝ ℂ)-
    (fourierL2 (burnolQuarterZeroExtension (actualGapResponse:BurnolQuarterIntervalL2)):TemperedDistribution ℝ ℂ)):=by
  simp only [map_smul,map_add,map_sub,Lp.toTemperedDistributionCLM_apply]
 change _=-(1/2:ℂ) • ((Lp.toTemperedDistributionCLM ℂ volume 2)
  ((2:ℂ) • (Seed.seed+burnolQuarterZeroExtension (T actualGapResponse:BurnolQuarterIntervalL2)-
   fourierL2 (burnolQuarterZeroExtension (actualGapResponse:BurnolQuarterIntervalL2)))))+_+_
 rw [rawRead]

 module

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
