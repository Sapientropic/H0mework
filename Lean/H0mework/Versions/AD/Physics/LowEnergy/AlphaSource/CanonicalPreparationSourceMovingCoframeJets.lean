import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingMeasureJets

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMovingNoetherReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreDifferential GaussQuantumMultiplier
open PreparationVacuumSpatialDensityTransport PreparationVacuumGradedTransport
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumSourceActionJets
open scoped Topology ContDiff BigOperators Matrix

-- Smoothness is recovered from the actual all-N identity, not supplied as a normalization premise.
theorem sourceSpatialVolumeReturn_smooth (f : Field289) (u : Parameter)
    (base : u.2∈physicalChart) (moved : fieldCoordinateCurve f u.1 u.2∈physicalChart)
    (v : SourceCoordinateSlice) :
    ContDiffAt ℝ ∞ (fun w : Parameter=>sourceSpatialVolumeReturn f w.1 w.2 v) u:=by
  have zero:=ratio_smooth f 0 u base moved (fun _=>v) contDiffAt_const
  have one:=ratio_smooth f 1 u base moved (fun _=>v) contDiffAt_const
  have generated:=Complex.reCLM.contDiff.contDiffAt.comp u (one.sub zero)
  apply generated.congr_of_eventuallyEq
  filter_upwards [sourceDomain_near f u base moved] with w hw
  change sourceSpatialVolumeReturn f w.1 w.2 v=Complex.re
    (spatialRatio f 1 w.1 w.2 v-spatialRatio f 0 w.1 w.2 v)
  rw [sourceSpatialRatio_generated f 1 w.1 ⟨w.2,hw.1⟩ hw.2 v,
    sourceSpatialRatio_generated f 0 w.1 ⟨w.2,hw.1⟩ hw.2 v]
  simp only [Complex.sub_re,Complex.ofReal_re]
  norm_num
  ring

theorem sourceSpatialGaugeReturn_smooth (f : Field289) (u : Parameter)
    (base : u.2∈physicalChart) (moved : fieldCoordinateCurve f u.1 u.2∈physicalChart)
    (v : SourceCoordinateSlice) :
    ContDiffAt ℝ ∞ (fun w : Parameter=>sourceSpatialGaugeReturn f w.1 w.2 v) u:=by
  have zero:=ratio_smooth f 0 u base moved (fun _=>v) contDiffAt_const
  have one:=ratio_smooth f 1 u base moved (fun _=>v) contDiffAt_const
  have generated:=Complex.reCLM.contDiff.contDiffAt.comp u
    (((contDiffAt_const (c:=(3:ℂ))).mul zero).sub ((contDiffAt_const (c:=(2:ℂ))).mul one))
  change ContDiffAt ℝ ∞ (fun w : Parameter=>Complex.re
    ((3:ℂ)*spatialRatio f 0 w.1 w.2 v-(2:ℂ)*spatialRatio f 1 w.1 w.2 v)) u at generated
  apply generated.congr_of_eventuallyEq
  filter_upwards [sourceDomain_near f u base moved] with w hw
  rw [sourceSpatialRatio_generated f 1 w.1 ⟨w.2,hw.1⟩ hw.2 v,
    sourceSpatialRatio_generated f 0 w.1 ⟨w.2,hw.1⟩ hw.2 v]
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
  norm_num
  ring

def sourceMovingCoframe (f : Field289) (a : QuantumTest) (i : Fin 6) (u : Parameter) : FockFiber:=
  (-Complex.I) • (fderiv ℝ a u.2 (GaussCoframeCore.coframeDirection i)+
    (sourceSpatialGaugeReturn f u.1 u.2 (GaussCoframeCore.coframeDirection i):ℂ) • a u.2+
      (sourceSpatialVolumeReturn f u.1 u.2 (GaussCoframeCore.coframeDirection i):ℂ) •
        (fiberNumber (a u.2)+(2:ℂ) • a u.2))

theorem sourceMovingCoframe_actual (f : Field289) (a : QuantumTest) (i : Fin 6) (u : Parameter)
    (base : u.2∈physicalChart) (moved : fieldCoordinateCurve f u.1 u.2∈physicalChart) :
    correctedCoframe f a i u=sourceMovingCoframe f a i u:=by
  change (-Complex.I) • (fderiv ℝ a u.2 (GaussCoframeCore.coframeDirection i)+
    spatialCorrection f (u.1,u.2) (GaussCoframeCore.coframeDirection i) (a u.2))=_
  rw [sourceSpatialCorrection_generated f u.1 ⟨u.2,base⟩ moved]
  simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply]
  simp only [sourceMovingCoframe,add_assoc]

def sourceMovingGaugeFirst (f : Field289) (z v : SourceCoordinateSlice) : ℝ:=
  deriv (fun r=>sourceSpatialGaugeReturn f r z v) 0

def sourceMovingVolumeFirst (f : Field289) (z v : SourceCoordinateSlice) : ℝ:=
  deriv (fun r=>sourceSpatialVolumeReturn f r z v) 0

def sourceMovingGaugeSecond (f : Field289) (z v : SourceCoordinateSlice) : ℝ:=
  deriv (deriv (fun r=>sourceSpatialGaugeReturn f r z v)) 0

def sourceMovingVolumeSecond (f : Field289) (z v : SourceCoordinateSlice) : ℝ:=
  deriv (deriv (fun r=>sourceSpatialVolumeReturn f r z v)) 0

private theorem sourceMovingGaugeCurve_smooth (f : Field289) (z : physicalChart) (v : SourceCoordinateSlice) :
    ∀ᶠr in 𝓝 (0:ℝ),ContDiffAt ℝ ∞ (fun t=>sourceSpatialGaugeReturn f t z.val v) r:=by
  filter_upwards [curve_valid_near f z] with r hr
  change ContDiffAt ℝ ∞ ((fun w : Parameter=>sourceSpatialGaugeReturn f w.1 w.2 v) ∘ (fun t : ℝ=>(t,z.val))) r
  exact (sourceSpatialGaugeReturn_smooth f (r,z.val) z.property hr v).comp r
    (contDiffAt_id.prodMk contDiffAt_const)

private theorem sourceMovingVolumeCurve_smooth (f : Field289) (z : physicalChart) (v : SourceCoordinateSlice) :
    ∀ᶠr in 𝓝 (0:ℝ),ContDiffAt ℝ ∞ (fun t=>sourceSpatialVolumeReturn f t z.val v) r:=by
  filter_upwards [curve_valid_near f z] with r hr
  change ContDiffAt ℝ ∞ ((fun w : Parameter=>sourceSpatialVolumeReturn f w.1 w.2 v) ∘ (fun t : ℝ=>(t,z.val))) r
  exact (sourceSpatialVolumeReturn_smooth f (r,z.val) z.property hr v).comp r
    (contDiffAt_id.prodMk contDiffAt_const)

private theorem sourceMovingCoframe_near (f : Field289) (a : QuantumTest) (i : Fin 6) (z : physicalChart) :
    (fun r=>correctedCoframe f a i (r,z.val))=ᶠ[𝓝 (0:ℝ)] fun r=>sourceMovingCoframe f a i (r,z.val):=by
  filter_upwards [curve_valid_near f z] with r hr
  exact sourceMovingCoframe_actual f a i (r,z.val) z.property hr

set_option backward.isDefEq.respectTransparency true in
private theorem sourceMovingCoframe_derivative_near (f : Field289) (a : QuantumTest) (i : Fin 6) (z : physicalChart) :
    ∀ᶠr in 𝓝 (0:ℝ),HasDerivAt (fun t=>sourceMovingCoframe f a i (t,z.val))
      ((-Complex.I) •
        (((deriv (fun t=>sourceSpatialGaugeReturn f t z.val (GaussCoframeCore.coframeDirection i)) r:ℝ):ℂ) • a z.val+
          ((deriv (fun t=>sourceSpatialVolumeReturn f t z.val (GaussCoframeCore.coframeDirection i)) r:ℝ):ℂ) •
            (fiberNumber (a z.val)+(2:ℂ) • a z.val))) r:=by
  filter_upwards [sourceMovingGaugeCurve_smooth f z (GaussCoframeCore.coframeDirection i),
    sourceMovingVolumeCurve_smooth f z (GaussCoframeCore.coframeDirection i)] with r hg hv
  have gauge:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r (hg.differentiableAt (by simp)).hasDerivAt
  have volume:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r (hv.differentiableAt (by simp)).hasDerivAt
  have actual:=((hasDerivAt_const r (fderiv ℝ a z.val (GaussCoframeCore.coframeDirection i))).add
    (gauge.smul_const (a z.val))).add
      (volume.smul_const (fiberNumber (a z.val)+(2:ℂ) • a z.val)) |>.const_smul (-Complex.I)
  convert! actual using 1
  simp only [zero_add]
  rfl

theorem sourceMovingCoframe_first (f : Field289) (a : QuantumTest) (i : Fin 6) (z : physicalChart) :
    deriv (fun r=>correctedCoframe f a i (r,z.val)) 0=
      (-Complex.I) • ((sourceMovingGaugeFirst f z.val (GaussCoframeCore.coframeDirection i):ℂ) • a z.val+
        (sourceMovingVolumeFirst f z.val (GaussCoframeCore.coframeDirection i):ℂ) •
          (fiberNumber (a z.val)+(2:ℂ) • a z.val)):=by
  exact ((sourceMovingCoframe_derivative_near f a i z).self_of_nhds.congr_of_eventuallyEq
    (sourceMovingCoframe_near f a i z)).deriv

theorem sourceMovingCoframe_second (f : Field289) (a : QuantumTest) (i : Fin 6) (z : physicalChart) :
    deriv (deriv (fun r=>correctedCoframe f a i (r,z.val))) 0=
      (-Complex.I) • ((sourceMovingGaugeSecond f z.val (GaussCoframeCore.coframeDirection i):ℂ) • a z.val+
        (sourceMovingVolumeSecond f z.val (GaussCoframeCore.coframeDirection i):ℂ) •
          (fiberNumber (a z.val)+(2:ℂ) • a z.val)):=by
  have gaugeSmooth:=(sourceMovingGaugeCurve_smooth f z (GaussCoframeCore.coframeDirection i)).self_of_nhds
  have volumeSmooth:=(sourceMovingVolumeCurve_smooth f z (GaussCoframeCore.coframeDirection i)).self_of_nhds
  have gaugeSecond:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    ((gaugeSmooth.derivWithin (m:=∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have volumeSecond:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    ((volumeSmooth.derivWithin (m:=∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have actual:=(gaugeSecond.smul_const (a z.val)).add
    (volumeSecond.smul_const (fiberNumber (a z.val)+(2:ℂ) • a z.val)) |>.const_smul (-Complex.I)
  have equalDeriv : deriv (fun r=>correctedCoframe f a i (r,z.val))=ᶠ[𝓝 (0:ℝ)]
      fun r=>(-Complex.I) •
        (((deriv (fun t=>sourceSpatialGaugeReturn f t z.val (GaussCoframeCore.coframeDirection i)) r:ℝ):ℂ) • a z.val+
          ((deriv (fun t=>sourceSpatialVolumeReturn f t z.val (GaussCoframeCore.coframeDirection i)) r:ℝ):ℂ) •
            (fiberNumber (a z.val)+(2:ℂ) • a z.val)):=by
    have pair:=(sourceMovingCoframe_near f a i z).eventuallyEq_nhds
    filter_upwards [sourceMovingCoframe_derivative_near f a i z,pair] with r hr he
    exact (hr.congr_of_eventuallyEq he).deriv
  exact (actual.congr_of_eventuallyEq equalDeriv).deriv

end LowEnergy.PreparationVacuumMovingNoetherReturn
