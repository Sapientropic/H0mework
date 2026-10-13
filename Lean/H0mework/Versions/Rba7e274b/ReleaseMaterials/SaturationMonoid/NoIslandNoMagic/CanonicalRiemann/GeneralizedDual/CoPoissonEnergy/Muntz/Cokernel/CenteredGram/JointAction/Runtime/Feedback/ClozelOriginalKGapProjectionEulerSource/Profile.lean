import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapProjectionEulerSource.Whole
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

namespace ConstructorPaid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszSource.Constructor (fourierRaw fourierDerivative fourierRaw_congr fourierRaw_continuous fourierRaw_hasDerivAt fourierDerivative_continuous truncatedFourier_read mean_zero compact compact_read compact_add zeroMean_read)
end ConstructorPaid
namespace EulerPaid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalCommonInverseForcing.InverseEuler (meanZeroRaw_continuous meanZeroRaw_hasDerivAt state_derivative_continuous eulerState meanZero_source_ward eulerState_add returnEuler endpointReaction)
end EulerPaid
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "μq" => volume.restrict (symmetricInterval q)

def actualGapSourceMean : ℂ:=burnolQuarterMeanCoefficient (burnolTruncatedFourier (intervalConstant q))
def actualGapSourceRaw : ℝ→ℂ:=
 ConstructorPaid.fourierRaw (fun _=>1)-fun _=>actualGapSourceMean
def actualGapSourceSlope : ℝ→ℂ:=ConstructorPaid.fourierDerivative (fun _=>1)

theorem actual_gap_source_read : (actualGapSource:BurnolQuarterIntervalL2)=ᵐ[μq] actualGapSourceRaw :=by
 have profile:=ConstructorPaid.fourierRaw_congr _ _ (intervalConstant_coeFn q)
 have raw: (burnolTruncatedFourier (intervalConstant q):ℝ→ℂ)=ᵐ[μq]
  ConstructorPaid.fourierRaw (fun _=>1) :=by
  rw [←profile]
  exact ConstructorPaid.truncatedFourier_read _
 have source:=burnolMeanZeroProjection_ae_raw (burnolTruncatedFourier (intervalConstant q)) _ raw
 change (burnolQuarterMeanZeroProjection (burnolTruncatedFourier (intervalConstant q)):ℝ→ℂ)=ᵐ[μq] _ at source
 have generated: (actualGapSource:BurnolQuarterIntervalL2)=burnolQuarterMeanZeroProjection (burnolTruncatedFourier (intervalConstant q)) :=by
  unfold actualGapSource burnolAmbientMeanZeroFourier
  rw [actual_seed_even_part]
  rfl
 rw [generated]
 exact source

theorem actual_gap_source_continuous : Continuous actualGapSourceRaw :=
 (ConstructorPaid.fourierRaw_continuous (fun _=>1) continuous_const).sub continuous_const
theorem actual_gap_source_slope_continuous : Continuous actualGapSourceSlope :=
 ConstructorPaid.fourierDerivative_continuous _ continuous_const
theorem actual_gap_source_derivative (x : ℝ) :
 HasDerivAt actualGapSourceRaw (actualGapSourceSlope x) x :=
 (ConstructorPaid.fourierRaw_hasDerivAt (fun _=>1) continuous_const x).sub_const _

def actualGapResponseRaw : ℝ→ℂ:=actualGapSourceRaw+burnolMeanZeroFourierRaw (T actualGapResponse)
def actualGapResponseSlope : ℝ→ℂ:=actualGapSourceSlope+
 ConstructorPaid.fourierDerivative (T actualGapResponse:BurnolQuarterIntervalL2)

theorem actual_gap_response_raw_continuous : Continuous actualGapResponseRaw :=
 actual_gap_source_continuous.add (EulerPaid.meanZeroRaw_continuous _)
theorem actual_gap_response_slope_continuous : Continuous actualGapResponseSlope :=
 actual_gap_source_slope_continuous.add (EulerPaid.state_derivative_continuous _)
theorem actual_gap_response_derivative (x : ℝ) :
 HasDerivAt actualGapResponseRaw (actualGapResponseSlope x) x :=
 (actual_gap_source_derivative x).add (EulerPaid.meanZeroRaw_hasDerivAt _ x)

theorem actual_gap_response_raw_read :
 (actualGapResponse:BurnolQuarterIntervalL2)=ᵐ[μq] actualGapResponseRaw :=by
 have generated:=actual_gap_response_equation
 change actualGapResponse-T (T actualGapResponse)=actualGapSource at generated
 have source:actualGapResponse=actualGapSource+T (T actualGapResponse):=by
  exact sub_eq_iff_eq_add.mp generated
 have read:=congrArg (fun state:BurnolQuarterMeanZeroCarrier=>(state:BurnolQuarterIntervalL2)) source
 rw [read]
 filter_upwards [Lp.coeFn_add (actualGapSource:BurnolQuarterIntervalL2)
   (T (T actualGapResponse):BurnolQuarterIntervalL2),actual_gap_source_read,
  burnolMeanZeroFourier_ae_raw (T actualGapResponse)] with x addition first second
 change ((actualGapSource:BurnolQuarterIntervalL2)+(T (T actualGapResponse):BurnolQuarterIntervalL2)) x=_
 rw [addition,Pi.add_apply,first,second]
 rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
