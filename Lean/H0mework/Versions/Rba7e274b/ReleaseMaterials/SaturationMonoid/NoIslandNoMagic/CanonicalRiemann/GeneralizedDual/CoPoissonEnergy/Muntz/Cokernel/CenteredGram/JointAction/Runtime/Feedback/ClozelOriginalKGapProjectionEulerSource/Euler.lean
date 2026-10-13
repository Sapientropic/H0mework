import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapProjectionEulerSource.Profile
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
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

namespace Profile
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward.ResponseProfile (etaRaw etaSlope etaMean eta_continuous eta_derivative eta_read)
end Profile
namespace WardPaid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalCommonInverseForcing.InverseEuler (raw_fourier_ward eulerRaw)
end WardPaid
local notation "μq" => volume.restrict (symmetricInterval q)

def actualGapSourceEuler : BurnolQuarterMeanZeroCarrier:=
 EulerPaid.eulerState actualGapSourceRaw actualGapSourceSlope
  actual_gap_source_continuous actual_gap_source_slope_continuous

def actualGapResponseEuler : BurnolQuarterMeanZeroCarrier:=
 EulerPaid.eulerState actualGapResponseRaw actualGapResponseSlope
  actual_gap_response_raw_continuous actual_gap_response_slope_continuous

/-- Actual Fourier constant source generates the endpoint eta action, including its centered mean. -/
theorem actual_gap_source_Euler_raw (x : ℝ) :
 WardPaid.eulerRaw actualGapSourceRaw actualGapSourceSlope x=
 Profile.etaRaw x+(1/2:ℂ)*actualGapSourceRaw x+Profile.etaMean :=by
 have ward:=WardPaid.raw_fourier_ward (fun _=>1) (fun _=>0)
  continuous_const continuous_const (fun t=>hasDerivAt_const t 1) x
 have scalar:WardPaid.eulerRaw (fun _=>1) (fun _=>0)=(fun _=>(1/2:ℂ)):=by
  funext t
  simp only [WardPaid.eulerRaw,mul_zero,mul_one,zero_add]
 rw [scalar] at ward
 have halfFourier:ConstructorPaid.fourierRaw (fun _=>(1/2:ℂ)) x=
  (1/2:ℂ)*ConstructorPaid.fourierRaw (fun _=>1) x :=by
  rw [OriginalRieszSource.Constructor.fourierRaw_integral,
   OriginalRieszSource.Constructor.fourierRaw_integral]
  have pointwise:(fun t:ℝ=>OriginalRieszSource.Constructor.phase x t*(1/2:ℂ))=
   fun t=>(1/2:ℂ)*(OriginalRieszSource.Constructor.phase x t*1):=by
   funext t;ring
  rw [pointwise,intervalIntegral.integral_const_mul]
 rw [halfFourier] at ward
 have constant:=ConstructorPaid.fourierRaw_congr _ _ (intervalConstant_coeFn q)
 have edge:=OriginalRieszSource.Edge.raw_apply q x
 rw [OriginalRieszSource.Constructor.phase_symm x q,
  OriginalRieszSource.Constructor.phase_symm x (-q)] at ward
 change _=Profile.etaRaw x+(1/2:ℂ)*actualGapSourceRaw x+Profile.etaMean
 unfold Profile.etaRaw actualGapSourceRaw actualGapSourceSlope WardPaid.eulerRaw
 dsimp only [Pi.sub_apply]
 change (x:ℂ)*ConstructorPaid.fourierDerivative (fun _=>1) x+
  (1/2:ℂ)*(ConstructorPaid.fourierRaw (fun _=>1) x-actualGapSourceMean)=
  OriginalRieszSource.Edge.raw q x-Profile.etaMean+
  (1/2:ℂ)*(ConstructorPaid.fourierRaw (fun _=>1) x-actualGapSourceMean)+Profile.etaMean
 rw [edge]
 change _=(q:ℂ)*(OriginalRieszSource.Constructor.phase x q+OriginalRieszSource.Constructor.phase x (-q))-
  ConstructorPaid.fourierRaw (intervalConstant q) x-Profile.etaMean+
  (1/2:ℂ)*(ConstructorPaid.fourierRaw (fun _=>1) x-actualGapSourceMean)+Profile.etaMean
 rw [constant,OriginalRieszSource.Constructor.phase_symm x q,
  OriginalRieszSource.Constructor.phase_symm x (-q)]
 linear_combination ward

/-- The source Euler field is generated from actual Fourier unit action, with constants removed only by its genuine mean-zero projection. -/
theorem actual_gap_source_Euler :
 actualGapSourceEuler=(1/2:ℂ) • actualGapSource+OriginalRieszSource.Response.eta :=by
 let rhs:BurnolQuarterIntervalL2:=
  (OriginalRieszSource.Response.eta:BurnolQuarterIntervalL2)+
  (1/2:ℂ) • (actualGapSource:BurnolQuarterIntervalL2)+Profile.etaMean • intervalConstant q
 have rawField:OriginalCommonInverseForcing.InverseEuler.eulerAmbient actualGapSourceRaw actualGapSourceSlope
  actual_gap_source_continuous actual_gap_source_slope_continuous=rhs :=by
  apply Lp.ext
  filter_upwards [ConstructorPaid.compact_read
    (WardPaid.eulerRaw actualGapSourceRaw actualGapSourceSlope)
    (OriginalCommonInverseForcing.InverseEuler.eulerRaw_continuous _ _ actual_gap_source_continuous actual_gap_source_slope_continuous),
   Lp.coeFn_add ((OriginalRieszSource.Response.eta:BurnolQuarterIntervalL2)+(1/2:ℂ) • (actualGapSource:BurnolQuarterIntervalL2))
    (Profile.etaMean • intervalConstant q),
   Lp.coeFn_add (OriginalRieszSource.Response.eta:BurnolQuarterIntervalL2) ((1/2:ℂ) • (actualGapSource:BurnolQuarterIntervalL2)),
   Lp.coeFn_smul (1/2:ℂ) (actualGapSource:BurnolQuarterIntervalL2),
   Lp.coeFn_smul Profile.etaMean (intervalConstant q),Profile.eta_read,actual_gap_source_read,intervalConstant_coeFn q]
   with x left whole pair scaled mean eta source unit
  change (ConstructorPaid.compact (WardPaid.eulerRaw actualGapSourceRaw actualGapSourceSlope)
   (OriginalCommonInverseForcing.InverseEuler.eulerRaw_continuous _ _ actual_gap_source_continuous actual_gap_source_slope_continuous)) x=
   (((OriginalRieszSource.Response.eta:BurnolQuarterIntervalL2)+(1/2:ℂ) • (actualGapSource:BurnolQuarterIntervalL2))+
   Profile.etaMean • intervalConstant q) x
  rw [left,whole,Pi.add_apply,pair,Pi.add_apply,scaled,Pi.smul_apply,mean,Pi.smul_apply,eta,source,unit]
  simp only [smul_eq_mul,mul_one]
  exact actual_gap_source_Euler_raw x
 unfold actualGapSourceEuler EulerPaid.eulerState
 rw [rawField]
 dsimp only [rhs]
 rw [map_add,map_add,map_smul,map_smul,OriginalRieszSource.Constructor.zeroMean_constant,smul_zero,add_zero]
 change _=(1/2:ℂ) • actualGapSource+OriginalRieszSource.Response.eta
 rw [show OriginalRieszSource.Constructor.zeroMean (OriginalRieszSource.Response.eta:BurnolQuarterIntervalL2)=
  OriginalRieszSource.Response.eta from Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _,
  show OriginalRieszSource.Constructor.zeroMean (actualGapSource:BurnolQuarterIntervalL2)=actualGapSource
  from Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _]
 exact add_comm _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
