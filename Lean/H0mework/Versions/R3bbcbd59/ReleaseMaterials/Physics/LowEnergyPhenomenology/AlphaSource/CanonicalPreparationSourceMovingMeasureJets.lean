import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePreparedSpinLoadedReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMovingNoetherReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumNumberRadialReturn PreparationVacuumGaussMeasureReturn
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussQuantumMultiplier
open PreparationVacuumSpatialDensityTransport PreparationVacuumGradedTransport
open PreparationVacuumFieldConstraintResponse CanonicalPreparationCore
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open scoped Topology ContDiff BigOperators Matrix

-- Both factors are those of the original full configuration measure.
def sourceMeasureGauge (z : SourceCoordinateSlice) : ℝ:=jacobian (z.2.2:Gauge)

def sourceMeasureGaugeSlope (z v : SourceCoordinateSlice) : ℝ:=
  fderiv ℝ sourceMeasureGauge z v/(2*sourceMeasureGauge z)

def sourceMeasureVolumeSlope (z v : SourceCoordinateSlice) : ℝ:=
  fderiv ℝ GaussNativeEnergy.volume z v/(2*GaussNativeEnergy.volume z)

theorem sourceMeasureGauge_smooth (z : physicalChart) : ContDiffAt ℝ ∞ sourceMeasureGauge z.val:=by
  have coordinates : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice=>(w.2.2:Gauge)):=
    coordinateSlice.subtypeL.contDiff.comp (contDiff_snd.comp contDiff_snd)
  exact (GaussDensityCore.jacobian_smooth z).comp z.val coordinates.contDiffAt

theorem sourceMeasureGauge_positive (z : physicalChart) : 0<sourceMeasureGauge z.val:=by
  have density:=GaussDensityCore.density_pos 0 z
  change 0<sourceMeasureGauge z.val*(GaussNativeEnergy.volume z.val)^2 at density
  exact (mul_pos_iff.mp density).resolve_right (fun h=>not_lt_of_ge (sq_nonneg _) h.2) |>.1

theorem sourceDensity_loggradient (N : ℕ) (z : physicalChart) (v : SourceCoordinateSlice) :
    fderiv ℝ (GaussDensityCore.density N) z.val v/GaussDensityCore.density N z.val=
      2*sourceMeasureGaugeSlope z.val v+2*(N+2:ℝ)*sourceMeasureVolumeSlope z.val v:=by
  have gauge:=((sourceMeasureGauge_smooth z).differentiableAt (by simp)).hasFDerivAt
  have volume:=(GaussNativeEnergy.volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z.val)
  have actual:=gauge.mul (volume.pow (N+2))
  change HasFDerivAt (GaussDensityCore.density N) _ z.val at actual
  rw [actual.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  rw [show N+2-1=N+1 from by omega]
  change ((sourceMeasureGauge z.val)*((N+2:ℝ)*(GaussNativeEnergy.volume z.val)^(N+1)*
      fderiv ℝ GaussNativeEnergy.volume z.val v)+
    (GaussNativeEnergy.volume z.val)^(N+2)*fderiv ℝ sourceMeasureGauge z.val v)/
      (sourceMeasureGauge z.val*(GaussNativeEnergy.volume z.val)^(N+2))=_
  have gaugeNonzero:=(sourceMeasureGauge_positive z).ne'
  have volumeNonzero:=(GaussNativeEnergy.volume_pos z).ne'
  simp only [sourceMeasureGaugeSlope,sourceMeasureVolumeSlope]
  field_simp
  rw [show N+2=(N+1)+1 from by omega,pow_succ]
  ring

theorem sourceHalfDensity_loggradient (N : ℕ) (z : physicalChart) (v : SourceCoordinateSlice) :
    fderiv ℝ (coreHalfDensity N) z.val v/coreHalfDensity N z.val=
      ((sourceMeasureGaugeSlope z.val v+(N+2:ℝ)*sourceMeasureVolumeSlope z.val v:ℝ):ℂ):=by
  have half:=((coreHalfDensity_smooth N z).differentiableAt (by simp)).hasFDerivAt
  have square:=half.mul half
  have nearby : (fun w=>coreHalfDensity N w*coreHalfDensity N w)=ᶠ[𝓝 z.val] GaussDensityCore.complexDensity N:=by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w inside
    simpa only [pow_two] using half_square N ⟨w,inside⟩
  have density:=((GaussDensityCore.complexDensity_smooth N z).differentiableAt (by simp)).hasFDerivAt
  have same:=congrArg (fun D : SourceCoordinateSlice→L[ℝ] ℂ=>D v)
    ((square.congr_of_eventuallyEq nearby.symm).unique density)
  simp only [add_apply,smul_apply,smul_eq_mul] at same
  have realDensity:=((GaussDensityCore.density_smooth N z).differentiableAt (by simp)).hasFDerivAt
  have complexDensity:=Complex.ofRealCLM.hasFDerivAt.comp z.val realDensity
  change HasFDerivAt (GaussDensityCore.complexDensity N) _ z.val at complexDensity
  have read:=sourceDensity_loggradient N z v
  have readComplex:=congrArg Complex.ofReal read
  push_cast at readComplex
  rw [complexDensity.fderiv] at same
  change coreHalfDensity N z.val*fderiv ℝ (coreHalfDensity N) z.val v+
    coreHalfDensity N z.val*fderiv ℝ (coreHalfDensity N) z.val v=
      (fderiv ℝ (GaussDensityCore.density N) z.val v:ℂ) at same
  have halfNonzero:=coreHalfDensity_ne_zero N z
  have densityNonzero:=Complex.ofReal_ne_zero.mpr (GaussDensityCore.density_pos N z).ne'
  have squared:=half_square N z
  change (coreHalfDensity N z.val)^2=(GaussDensityCore.density N z.val:ℂ) at squared
  have densityRead : (fderiv ℝ (GaussDensityCore.density N) z.val v:ℂ)=
      (2:ℂ)*((sourceMeasureGaugeSlope z.val v:ℂ)+(N+2:ℂ)*(sourceMeasureVolumeSlope z.val v:ℂ))*
        (coreHalfDensity N z.val)^2:=by
    have cleared:=(div_eq_iff densityNonzero).mp readComplex
    rw [←squared] at cleared
    convert! cleared using 1
    ring
  have relation : (2*coreHalfDensity N z.val)*
      (fderiv ℝ (coreHalfDensity N) z.val v-
        ((sourceMeasureGaugeSlope z.val v:ℂ)+(N+2:ℂ)*(sourceMeasureVolumeSlope z.val v:ℂ))*coreHalfDensity N z.val)=0:=by
    linear_combination same+densityRead
  have zeroDifference:=(mul_eq_zero.mp relation).resolve_left (mul_ne_zero (by norm_num) halfNonzero)
  apply (div_eq_iff halfNonzero).mpr
  simpa only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_ofNat] using sub_eq_zero.mp zeroDifference

def sourceSpatialGaugeReturn (f : Field289) (r : ℝ) (z v : SourceCoordinateSlice) : ℝ:=
  sourceMeasureGaugeSlope z v-sourceMeasureGaugeSlope (fieldCoordinateCurve f r z) (shiftedDirection f r z v)

def sourceSpatialVolumeReturn (f : Field289) (r : ℝ) (z v : SourceCoordinateSlice) : ℝ:=
  sourceMeasureVolumeSlope z v-sourceMeasureVolumeSlope (fieldCoordinateCurve f r z) (shiftedDirection f r z v)

theorem sourceSpatialRatio_generated (f : Field289) (N : ℕ) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (v : SourceCoordinateSlice) :
    spatialRatio f N r z.val v=
      ((sourceSpatialGaugeReturn f r z.val v+(N+2:ℝ)*sourceSpatialVolumeReturn f r z.val v:ℝ):ℂ):=by
  rw [spatialRatio_source f N r z moved v,sourceHalfDensity_loggradient,
    sourceHalfDensity_loggradient N ⟨_,moved⟩]
  simp only [sourceSpatialGaugeReturn,sourceSpatialVolumeReturn]
  push_cast
  ring

theorem sourceSpatialCorrection_generated (f : Field289) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (v : SourceCoordinateSlice) :
    spatialCorrection f (r,z.val) v=
      (sourceSpatialGaugeReturn f r z.val v:ℂ) • ContinuousLinearMap.id ℂ FockFiber+
        (sourceSpatialVolumeReturn f r z.val v:ℂ) •
          (fiberNumber+(2:ℂ) • ContinuousLinearMap.id ℂ FockFiber):=by
  apply ContinuousLinearMap.ext
  intro psi
  apply PiLp.ext
  intro word
  change spatialRatio f word.card r z.val v*psi word=_
  rw [sourceSpatialRatio_generated f word.card r z moved v]
  simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply,PiLp.add_apply,
    PiLp.smul_apply,fiberNumber_apply,smul_eq_mul]
  push_cast
  ring

def sourceFieldCoordinateJacobian (f : Field289) (r : ℝ) (z : SourceCoordinateSlice) :
    SourceCoordinateSlice→L[ℝ] SourceCoordinateSlice:=
  ContinuousLinearMap.id ℝ SourceCoordinateSlice+r • fderiv ℝ (fieldVector f) z

theorem sourceFieldCoordinateJacobian_actual (f : Field289) (r : ℝ) (z : physicalChart) :
    fderiv ℝ (fieldCoordinateCurve f r) z.val=sourceFieldCoordinateJacobian f r z.val:=by
  have actual:=hasFDerivAt_id z.val |>.add
    (((fieldVector_smooth f z).differentiableAt (by simp)).hasFDerivAt.const_smul r)
  change HasFDerivAt (fieldCoordinateCurve f r) _ z.val at actual
  exact actual.fderiv

theorem sourceFieldCoordinateJacobian_direction (f : Field289) (r : ℝ) (z v : SourceCoordinateSlice) :
    sourceFieldCoordinateJacobian f r z v=shiftedDirection f r z v:=rfl

theorem sourceMovingHalfDensity_gradient (f : Field289) (N : ℕ) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (v : SourceCoordinateSlice) :
    fderiv ℝ (fun w=>coreHalfDensity N (fieldCoordinateCurve f r w)) z.val v/
        coreHalfDensity N (fieldCoordinateCurve f r z.val)=
      ((sourceMeasureGaugeSlope (fieldCoordinateCurve f r z.val) (shiftedDirection f r z.val v)+
        (N+2:ℝ)*sourceMeasureVolumeSlope (fieldCoordinateCurve f r z.val) (shiftedDirection f r z.val v):ℝ):ℂ):=by
  have curve:=hasFDerivAt_id z.val |>.add
    (((fieldVector_smooth f z).differentiableAt (by simp)).hasFDerivAt.const_smul r)
  change HasFDerivAt (fieldCoordinateCurve f r) _ z.val at curve
  have actual:=((coreHalfDensity_smooth N ⟨_,moved⟩).differentiableAt (by simp)).hasFDerivAt.comp z.val curve
  change HasFDerivAt (fun w=>coreHalfDensity N (fieldCoordinateCurve f r w)) _ z.val at actual
  rw [actual.fderiv]
  change fderiv ℝ (coreHalfDensity N) (fieldCoordinateCurve f r z.val) (shiftedDirection f r z.val v)/
    coreHalfDensity N (fieldCoordinateCurve f r z.val)=_
  exact sourceHalfDensity_loggradient N ⟨_,moved⟩ _

end LowEnergy.PreparationVacuumMovingNoetherReturn
