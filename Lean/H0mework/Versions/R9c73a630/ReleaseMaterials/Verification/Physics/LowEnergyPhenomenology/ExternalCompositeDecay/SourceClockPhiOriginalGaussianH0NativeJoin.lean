import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0RealPrimitives
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0KineticPrimitives
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceClockPhiOriginalGaussianH0NativeJoin
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockPhiCombinedScalePressure SourceClockPhiMatchedDiffusionSource
open SourceClockPhiOriginalGaussianH0Recognition SourceClockPhiOriginalGaussianH0FirstJet
open SourceClockPhiOriginalGaussianH0RealPrimitives SourceClockPhiOriginalGaussianH0KineticPrimitives
open SourceScalarVirialBulk SourceScalarDoubleCurrent
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev a:End:=inverseRootAction
private abbrev LV:End:=SourceClockPhiCoframeForwardCore.forwardGenerator

theorem scalar_kinetic_complete_current:
    completeCurrent scalarKinetic=(-14:ℂ) • (U*scalarKinetic):=by
  obtain ⟨hU,ha,hD,hL⟩:=scalar_kinetic_primitives
  have h:=complete_current_homogeneous scalarKinetic (-2/3) 2 hU ha
    hD
    (by convert hL using 1; norm_num)
  simpa only [show (2:ℂ)*2-3*2+18*(-2/3)=(-14:ℂ) by norm_num] using h
theorem gauge_kinetic_complete_current:
    completeCurrent gaugeKinetic=(22:ℂ) • (U*gaugeKinetic):=by
  obtain ⟨hU,ha,hD,hL⟩:=gauge_kinetic_primitives
  have h:=complete_current_homogeneous gaugeKinetic (2/3) (-2) hU ha
    (by simpa only [neg_neg] using hD)
    (by convert hL using 1; norm_num)
  simpa only [show (-2:ℂ)*(-2)-3*(-2)+18*(2/3)=(22:ℂ) by norm_num] using h
theorem matter_complete_current:
    completeCurrent GaussMatterCore.matterAction=(-2:ℂ) • (U*GaussMatterCore.matterAction):=by
  obtain ⟨hU,ha,hD,hL⟩:=matter_primitives
  have h:=complete_current_homogeneous GaussMatterCore.matterAction 0 1 hU ha
    hD
    (by convert hL using 1; norm_num)
  simpa only [show (1:ℂ)*1-3*1+18*0=(-2:ℂ) by norm_num] using h

theorem completeCurrent_add(X Y:End):
    completeCurrent (X+Y)=completeCurrent X+completeCurrent Y:=by
  unfold completeCurrent diffusionCurrent diffusionDriftTranspose diffusionDrift
  noncomm_ring
  module
theorem completeCurrent_smul(c:ℂ)(X:End):
    completeCurrent (c • X)=c • completeCurrent X:=by
  unfold completeCurrent diffusionCurrent diffusionDriftTranspose diffusionDrift
  simp only [mul_smul_comm,smul_mul_assoc,smul_add,smul_sub]
  noncomm_ring
  module
theorem completeCurrent_sub(X Y:End):
    completeCurrent (X-Y)=completeCurrent X-completeCurrent Y:=by
  unfold completeCurrent diffusionCurrent diffusionDriftTranspose diffusionDrift
  noncomm_ring
  module
def nativeBase:End:=
  scalarKinetic+gaugeKinetic+GaussMatterCore.matterAction+centeredAction-
  (2:ℂ) • vacuumLinearAction+vacuumConstantAction+scalarSpatialAction+magneticAction

theorem native_eight_jet_eq_completeCurrent(f g:QuantumTest):
    nativePairJet f g=sourcePair f (completeCurrent nativeBase g):=by
  have hq:completeCurrent nativeBase=
      (-14:ℂ) • (U*scalarKinetic)+(22:ℂ) • (U*gaugeKinetic)+
      (-2:ℂ) • (U*GaussMatterCore.matterAction)+(34:ℂ) • (U*centeredAction)-
      (56:ℂ) • (U*vacuumLinearAction)+(24:ℂ) • (U*vacuumConstantAction)+
      (12:ℂ) • (U*scalarSpatialAction)+(16:ℂ) • (U*magneticAction):=by
    unfold nativeBase
    simp only [completeCurrent_add,completeCurrent_sub,completeCurrent_smul]
    rw [scalar_kinetic_complete_current,gauge_kinetic_complete_current,
      matter_complete_current,centered_complete_current,vacuum_linear_complete_current,
      vacuum_constant_complete_current,scalar_spatial_complete_current,
      magnetic_complete_current]
    module
  rw [hq]
  unfold nativePairJet
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.mul_apply,sourcePair,map_add,map_sub,map_smul,
    inner_add_right,inner_sub_right,inner_smul_right]

end LowEnergy.SourceClockPhiOriginalGaussianH0NativeJoin
