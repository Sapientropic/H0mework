import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationRelativeDensity
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationNativeMeasure

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDensityTrace
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussDensityCore CanonicalPreparationCore
open PreparationVacuumLowerLeaves PreparationMeasure
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open scoped ContDiff Topology

def sourceDensityFactor : ℝ :=
  sourceJacobian/originalRho3 SourceQuantumConfigurationHilbert.sourceGauge

theorem sourceDensityFactor_positive : 0<sourceDensityFactor := by
  unfold sourceDensityFactor
  rw [originalRho3_source]
  exact div_pos source_jacobian_pos (pow_pos gaugeScale_pos _)

def rho3OnConfiguration (z : SourceCoordinateSlice) : ℝ := originalRho3 (z.2.2 : Gauge)
def literalDensity (N : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  rho3OnConfiguration z*volume z^(N+2)
def literalHalf (z : SourceCoordinateSlice) : ℝ := volume z*Real.sqrt (rho3OnConfiguration z)

theorem rho3OnConfiguration_positive (z : physicalChart) : 0<rho3OnConfiguration z.val := by
  rw [rho3OnConfiguration,originalRho3_native]
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos z.property.2.2.2.2.1))
    z.property.2.2.2.2.2.1

theorem rho3OnConfiguration_smooth : ContDiff ℝ ∞ rho3OnConfiguration := by
  have gauge : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => (w.2.2 : Gauge)) :=
    coordinateSlice.subtypeL.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have first:=firstGauge.toContinuousLinearMap.contDiff.comp gauge
  have second:=secondGauge.toContinuousLinearMap.contDiff.comp gauge
  have formula : rho3OnConfiguration=(fun w : SourceCoordinateSlice =>
      8*(firstGauge (w.2.2 : Gauge))^2*secondGauge (w.2.2 : Gauge)) := by
    funext w
    exact originalRho3_native _
  rw [formula]
  exact (contDiff_const.mul (first.pow 2)).mul second

theorem originalDensity_feed (N : ℕ) (z : physicalChart) :
    density N z.val=sourceDensityFactor*literalDensity N z.val := by
  rw [density,originalJacobian_density z.val.2.2 z.property.2.2.2.2.1 z.property.2.2.2.2.2.1]
  unfold sourceDensityFactor literalDensity rho3OnConfiguration volume
  ring

theorem literalHalf_positive (z : physicalChart) : 0<literalHalf z.val :=
  mul_pos (volume_pos z) (Real.sqrt_pos.mpr (rho3OnConfiguration_positive z))

theorem literalHalf_smooth (z : physicalChart) : ContDiffAt ℝ ∞ literalHalf z.val :=
  volume_smooth.contDiffAt.mul
    (rho3OnConfiguration_smooth.contDiffAt.sqrt (rho3OnConfiguration_positive z).ne')

theorem originalHalf_feed (z : physicalChart) :
    realSourceHalf z.val=Real.sqrt sourceDensityFactor*literalHalf z.val := by
  rw [realSourceHalf,originalDensity_feed]
  unfold literalDensity literalHalf
  norm_num
  rw [Real.sqrt_mul sourceDensityFactor_positive.le,
    Real.sqrt_mul (rho3OnConfiguration_positive z).le,Real.sqrt_sq (volume_pos z).le]
  ring

theorem originalHalfLog_feed (D : SourceCoordinateSlice) (z : physicalChart) :
    (realSourceHalf z.val)⁻¹*fderiv ℝ realSourceHalf z.val D=
      (literalHalf z.val)⁻¹*fderiv ℝ literalHalf z.val D := by
  have equal : realSourceHalf=ᶠ[𝓝 z.val]
      (fun w => Real.sqrt sourceDensityFactor*literalHalf w) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact originalHalf_feed ⟨w,hw⟩
  have product := (((literalHalf_smooth z).differentiableAt (by simp)).hasFDerivAt.const_mul
    (Real.sqrt sourceDensityFactor)).fderiv
  rw [originalHalf_feed,equal.fderiv_eq,product]
  simp only [smul_apply,smul_eq_mul]
  have nonzero:Real.sqrt sourceDensityFactor≠0 := (Real.sqrt_pos.mpr sourceDensityFactor_positive).ne'
  field_simp

theorem original_rawHalfLog_feed (i : Fin 100) (z : physicalChart) :
    rawHalfLog i z.val=(literalHalf z.val)⁻¹*fderiv ℝ literalHalf z.val (rawDirection i) :=
  originalHalfLog_feed _ z

theorem original_complexHalfLog_feed (D : SourceCoordinateSlice) (z : physicalChart) :
    sourceHalfLog D z.val=
      ((literalHalf z.val)⁻¹*fderiv ℝ literalHalf z.val D : ℝ) := by
  have derivative:=Complex.ofRealCLM.hasFDerivAt.comp z.val
    ((realSourceHalf_smooth z).differentiableAt (by simp)).hasFDerivAt
  have read : fderiv ℝ sourceHalf z.val=
      Complex.ofRealCLM.comp (fderiv ℝ realSourceHalf z.val) := by
    simpa only [sourceHalf,coreHalfDensity,realSourceHalf] using! derivative.fderiv
  unfold sourceHalfLog
  rw [read]
  change (realSourceHalf z.val : ℂ)⁻¹*
    (fderiv ℝ realSourceHalf z.val D : ℂ)=_
  rw [←Complex.ofReal_inv,←Complex.ofReal_mul,originalHalfLog_feed]

theorem original_rawDensity_feed (N : ℕ) (z : physicalChart) :
    nativeVolumeFactor*density N z.val=
      (nativeVolumeFactor*sourceDensityFactor)*literalDensity N z.val := by
  rw [originalDensity_feed]
  ring

theorem original_rawHalf_feed (z : physicalChart) :
    Real.sqrt nativeVolumeFactor*realSourceHalf z.val=
      Real.sqrt (nativeVolumeFactor*sourceDensityFactor)*literalHalf z.val := by
  rw [originalHalf_feed,Real.sqrt_mul nativeVolumeFactor_pos.le]
  ring

end LowEnergy.PreparationVacuumDensityTrace
