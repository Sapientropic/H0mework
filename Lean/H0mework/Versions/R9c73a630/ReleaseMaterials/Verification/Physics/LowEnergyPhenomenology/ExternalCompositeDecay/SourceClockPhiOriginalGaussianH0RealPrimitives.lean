import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0Recognition
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceClockPhiOriginalGaussianH0RealPrimitives
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarVirialBulk SourceScalarGaugeScale SourceGaugeRadialCurrent SourceGaugeRadialPair
open SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceClockPhiOriginalGaussianH0Recognition SourceClockPhiOriginalGaussianH0FirstJet
open SourcePhysicalKineticSquare SourceClockPhiCombinedScalePressure SourceHamiltonianScaleJet
open SourceKineticScale
open Filter
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
def phiScale (r:ℝ)(z:SourceCoordinateSlice):SourceCoordinateSlice:=
  (z.1,r • (vacuumSlice+z.2.1)-vacuumSlice,z.2.2)
private theorem phi_scale_one(z:SourceCoordinateSlice):phiScale 1 z=z:=by simp [phiScale]
private theorem phi_scale_derivative(z:SourceCoordinateSlice):
    HasDerivAt (fun r=>phiScale r z) (phiEuler z) 1:=by
  simpa only [phiScale,phiEuler,id_eq,one_smul] using!
    (hasDerivAt_const (1:ℝ) z.1).prodMk
      ((((hasDerivAt_id (1:ℝ)).smul_const (vacuumSlice+z.2.1)).sub_const vacuumSlice).prodMk
        (hasDerivAt_const (1:ℝ) z.2.2))
private theorem homogeneous_multiplier(E:End)(e:SourceCoordinateSlice→SourceCoordinateSlice)
    (flow:ℝ→SourceCoordinateSlice→SourceCoordinateSlice)
    (hE:∀f z,E f z=fderiv ℝ f z (e z))
    (hg:∀z,HasDerivAt (fun r=>flow r z) (e z) 1)(h1:∀z,flow 1 z=z)
    (A:End)(B:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber)(p:ℕ)
    (law:∀f z,A f z=B z (f z))(hp:∀r z,B (flow r z)=((r^p:ℝ):ℂ) • B z):
    E*A-A*E=(p:ℂ) • A:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hf:=(f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (hg z) (h1 z).symm
  have hA:=((A f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (hg z) (h1 z).symm
  have hb:=(B z).restrictScalars ℝ |>.hasFDerivAt |>.comp_hasDerivAt 1 hf
  have hr:HasDerivAt (fun r:ℝ=>((r^p:ℝ):ℂ)) (p:ℂ) 1:=by
    have h:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 1 ((hasDerivAt_id (1:ℝ)).pow p)
    simpa only [Function.comp_def,id_eq,one_pow,mul_one,Complex.ofRealCLM_apply,
      Complex.ofReal_natCast] using! h
  have hh:=hr.smul hb
  have hx:(fun r=>A f (flow r z))=(fun r:ℝ=>((r^p:ℝ):ℂ) • B z (f (flow r z))):=by
    funext r
    rw [law,hp]
    rfl
  change HasDerivAt (fun r=>A f (flow r z)) _ 1 at hA
  rw [hx] at hA
  have hu:=hA.unique hh
  simp only [Function.comp_def,one_pow,Complex.ofReal_one,one_smul,h1,
    ContinuousLinearMap.coe_restrictScalars'] at hu
  change E (A f) z-A (E f) z=(p:ℂ) • A f z
  rw [hE,law,hE,law,hu]
  exact add_sub_cancel_left _ _
private theorem phi_real_degree(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(p:ℕ)
    (hp:∀r z,b (phiScale r z)=r^p*b z):
    deltaPhi (multiply b hb)=(p:ℂ) • multiply b hb:=by
  apply homogeneous_multiplier phiEulerAction phiEuler phiScale phi_euler_apply
    phi_scale_derivative phi_scale_one (multiply b hb)
    (fun z=>(b z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) p (fun _ _=>rfl)
  intro r z
  rw [hp,Complex.ofReal_mul,smul_smul]
private theorem gauge_real_degree(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(p:ℕ)
    (hp:∀r z,b (gaugeScale r z)=r^p*b z):
    deltaGauge (multiply b hb)=(p:ℂ) • multiply b hb:=by
  apply homogeneous_multiplier gaugeEulerAction gaugeEuler gaugeScale gauge_euler_apply
    (fun z=>gauge_scale_derivative z 1) gauge_scale_one (multiply b hb)
    (fun z=>(b z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) p (fun _ _=>rfl)
  intro r z
  rw [hp,Complex.ofReal_mul,smul_smul]

theorem phi_invariant_local(A:End)(B:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber)
    (law:∀f z,A f z=B z (f z))(hB:∀r z,B (phiScale r z)=B z):
    deltaPhi A=0:=by
  have h:=homogeneous_multiplier phiEulerAction phiEuler phiScale phi_euler_apply
    phi_scale_derivative phi_scale_one A B 0 law (fun r z=>by simpa using hB r z)
  change phiEulerAction*A-A*phiEulerAction=0
  simpa only [Nat.cast_zero,zero_smul] using h
theorem gauge_invariant_local(A:End)(B:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber)
    (law:∀f z,A f z=B z (f z))(hB:∀r z,B (gaugeScale r z)=B z):
    deltaGauge A=0:=by
  have h:=homogeneous_multiplier gaugeEulerAction gaugeEuler gaugeScale gauge_euler_apply
    (fun z=>gauge_scale_derivative z 1) gauge_scale_one A B 0 law
    (fun r z=>by simpa using hB r z)
  change gaugeEulerAction*A-A*gaugeEulerAction=0
  simpa only [Nat.cast_zero,zero_smul] using h

private theorem scale_real_degree(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(k:ℤ)
    (hk:∀r z,r≠0→b (SourceCoframeVolume.scale r z)=r^k*b z):
    scaleDerivative (multiply b hb)=(k:ℂ) • multiply b hb:=by
  have he(z:physicalChart):fderiv ℝ b z.val (SourceCoframeVolume.euler z.val)=
      (k:ℝ)*b z.val:=
    SourceKineticScale.euler_of_scale b k z (hb z) (fun r hr=>hk r z.val hr)
  have h:=SourceDilationMultiplier.homogeneous_multiplier b hb (k:ℝ) he
  change (3*Complex.I/2:ℂ) •
    (SourceCoframeVolumeCurrent.dilation*multiply b hb-
      multiply b hb*SourceCoframeVolumeCurrent.dilation)=_
  rw [h,smul_smul]
  congr 1
  push_cast
  calc
    (3*Complex.I/2)*((-2*Complex.I/3)*(k:ℂ))=
        -(Complex.I*Complex.I)*(k:ℂ):=by ring
    _=_:=by rw [Complex.I_mul_I];ring

theorem complete_current_multiplier_degrees(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (m n:ℕ)(k:ℤ)(p q:ℂ)
    (hphi:∀r z,b (phiScale r z)=r^m*b z)
    (hgauge:∀r z,b (gaugeScale r z)=r^n*b z)
    (hcoframe:∀r z,r≠0→b (SourceCoframeVolume.scale r z)=r^k*b z)
    (hq:(m:ℂ)-(n:ℂ)= -q)(hk:(k:ℂ)=3*p-1):
    SourceClockPhiMatchedDiffusionSource.completeCurrent (multiply b hb)=
      (q*q-3*q+18*p) • (U*(multiply b hb)):=by
  have hp:=phi_real_degree b hb m hphi
  have hg:=gauge_real_degree b hb n hgauge
  have hs:=scale_real_degree b hb k hcoframe
  have hD:deltaPhi (multiply b hb)-deltaGauge (multiply b hb)=(-q) • multiply b hb:=by
    rw [hp,hg]
    rw [←sub_smul,hq]
  have hS:scaleDerivative (multiply b hb)=(3*p-1) • multiply b hb:=by
    rw [hs,hk]
  exact complete_current_real_multiplier b hb p q hD hS

private def centerValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*volume z*‖scalarField z‖^2
private theorem center_smooth(z:physicalChart):ContDiffAt ℝ ∞ centerValue z.val:=
  (contDiffAt_const.mul volume_smooth.contDiffAt).mul (scalarField_smooth.norm_sq ℝ).contDiffAt
private theorem phi_field(r:ℝ)(z:SourceCoordinateSlice):
    scalarField (phiScale r z)=r • scalarField z:=by
  change vacuum+(r • (vacuum+(z.2.1:Scalar))-vacuum)=r • (vacuum+(z.2.1:Scalar))
  abel
private theorem center_phi(r:ℝ)(z:SourceCoordinateSlice):
    centerValue (phiScale r z)=r^2*centerValue z:=by
  change sourceTime 0*volume z*‖scalarField (phiScale r z)‖^2=_
  rw [phi_field,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  unfold centerValue
  ring
private theorem center_gauge(r:ℝ)(z:SourceCoordinateSlice):
    centerValue (gaugeScale r z)=r^0*centerValue z:=by
  simp only [pow_zero,one_mul]
  rfl
private theorem center_coframe(r:ℝ)(z:SourceCoordinateSlice)(_hr:r≠0):
    centerValue (SourceCoframeVolume.scale r z)=r^(3:ℤ)*centerValue z:=by
  unfold centerValue
  rw [volume_scale]
  change sourceTime 0*(r^3*volume z)*‖scalarField z‖^2=_
  ac_rfl
theorem centered_complete_current:
    SourceClockPhiMatchedDiffusionSource.completeCurrent centeredAction=
      (34:ℂ) • (U*centeredAction):=by
  have he:centeredAction=multiply centerValue center_smooth:=rfl
  rw [he]
  have h:=complete_current_multiplier_degrees centerValue center_smooth 2 0 3 (4/3) (-2)
    center_phi center_gauge center_coframe (by norm_num) (by norm_num)
  simpa only [show (-2:ℂ)*(-2)-3*(-2)+18*(4/3)=34 by norm_num] using h

private def vacLinValue(z:SourceCoordinateSlice):ℝ:=
  sourceTime 0*volume z*inner ℝ vacuum (scalarField z)
private theorem vacLin_smooth(z:physicalChart):ContDiffAt ℝ ∞ vacLinValue z.val:=
  (contDiffAt_const.mul volume_smooth.contDiffAt).mul
    (contDiff_const.inner ℝ scalarField_smooth).contDiffAt
private theorem vacLin_phi(r:ℝ)(z:SourceCoordinateSlice):
    vacLinValue (phiScale r z)=r^1*vacLinValue z:=by
  change sourceTime 0*volume z*inner ℝ vacuum (scalarField (phiScale r z))=_
  rw [phi_field,real_inner_smul_right,pow_one]
  unfold vacLinValue
  ring
private theorem vacLin_gauge(r:ℝ)(z:SourceCoordinateSlice):
    vacLinValue (gaugeScale r z)=r^0*vacLinValue z:=by
  simp only [pow_zero,one_mul]
  rfl
private theorem vacLin_coframe(r:ℝ)(z:SourceCoordinateSlice)(_hr:r≠0):
    vacLinValue (SourceCoframeVolume.scale r z)=r^(3:ℤ)*vacLinValue z:=by
  unfold vacLinValue
  rw [volume_scale]
  change sourceTime 0*(r^3*volume z)*inner ℝ vacuum (scalarField z)=_
  ac_rfl
theorem vacuum_linear_complete_current:
    SourceClockPhiMatchedDiffusionSource.completeCurrent vacuumLinearAction=
      (28:ℂ) • (U*vacuumLinearAction):=by
  have he:vacuumLinearAction=multiply vacLinValue vacLin_smooth:=rfl
  rw [he]
  have h:=complete_current_multiplier_degrees vacLinValue vacLin_smooth 1 0 3 (4/3) (-1)
    vacLin_phi vacLin_gauge vacLin_coframe (by norm_num) (by norm_num)
  simpa only [show (-1:ℂ)*(-1)-3*(-1)+18*(4/3)=28 by norm_num] using h

private def volumeMultiple(c:ℝ)(z:SourceCoordinateSlice):ℝ:=c*volume z
private theorem volumeMultiple_smooth(c:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (volumeMultiple c) z.val:=
  contDiffAt_const.mul volume_smooth.contDiffAt
private theorem volumeMultiple_phi(c r:ℝ)(z:SourceCoordinateSlice):
    volumeMultiple c (phiScale r z)=r^0*volumeMultiple c z:=by
  simp only [pow_zero,one_mul]
  rfl
private theorem volumeMultiple_gauge(c r:ℝ)(z:SourceCoordinateSlice):
    volumeMultiple c (gaugeScale r z)=r^0*volumeMultiple c z:=by
  simp only [pow_zero,one_mul]
  rfl
private theorem volumeMultiple_coframe(c r:ℝ)(z:SourceCoordinateSlice)(_hr:r≠0):
    volumeMultiple c (SourceCoframeVolume.scale r z)=r^(3:ℤ)*volumeMultiple c z:=by
  unfold volumeMultiple
  rw [volume_scale]
  ac_rfl
private theorem volumeMultiple_complete_current(c:ℝ):
    SourceClockPhiMatchedDiffusionSource.completeCurrent
      (multiply (volumeMultiple c) (volumeMultiple_smooth c))=
      (24:ℂ) • (U*(multiply (volumeMultiple c) (volumeMultiple_smooth c))):=by
  have h:=complete_current_multiplier_degrees (volumeMultiple c) (volumeMultiple_smooth c)
    0 0 3 (4/3) 0 (volumeMultiple_phi c) (volumeMultiple_gauge c)
    (volumeMultiple_coframe c) (by norm_num) (by norm_num)
  simpa only [show (0:ℂ)*0-3*0+18*(4/3)=24 by norm_num] using h
theorem vacuum_constant_complete_current:
    SourceClockPhiMatchedDiffusionSource.completeCurrent vacuumConstantAction=
      (24:ℂ) • (U*vacuumConstantAction):=by
  have he:vacuumConstantAction=
      multiply (volumeMultiple (sourceTime 0*‖vacuum‖^2))
        (volumeMultiple_smooth (sourceTime 0*‖vacuum‖^2)):=by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change ((sourceTime 0*volume z*‖vacuum‖^2:ℝ):ℂ) • f z=
      (((sourceTime 0*‖vacuum‖^2)*volume z:ℝ):ℂ) • f z
    congr 1
    ring
  rw [he]
  exact volumeMultiple_complete_current _
theorem coframe_volume_complete_current:
    SourceClockPhiMatchedDiffusionSource.completeCurrent
      (multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth)=
      (24:ℂ) • (U*(multiply GaussCoframeForm.volumePotential
        GaussCoframeForm.volumePotential_smooth)):=by
  have he:multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth=
      multiply (volumeMultiple (3*sourceTime 0)) (volumeMultiple_smooth (3*sourceTime 0)):=rfl
  rw [he]
  exact volumeMultiple_complete_current _

private def spatialValue(z:SourceCoordinateSlice):ℝ:=
  -(sourceTime 0*volume z/2*∑i:Fin 3,∑j:Fin 3,
    inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j))
private theorem spatial_smooth(z:physicalChart):ContDiffAt ℝ ∞ spatialValue z.val:=by
  apply ContDiffAt.neg
  exact (contDiffAt_const.mul volume_smooth.contDiffAt |>.div_const 2).mul
    (ContDiffAt.sum (fun i _=>ContDiffAt.sum (fun j _=>
      (inverseSpatial_smooth i j z).mul
        ((scalarGradient_smooth i).contDiffAt.inner ℝ (scalarGradient_smooth j).contDiffAt))))
private theorem spatial_coframe(r:ℝ)(z:SourceCoordinateSlice)(hr:r≠0):
    spatialValue (SourceCoframeVolume.scale r z)=r^(1:ℤ)*spatialValue z:=by
  have hgrad(i:Fin 3):scalarGradient (SourceCoframeVolume.scale r z) i=scalarGradient z i:=rfl
  simp only [spatialValue,volume_scale,inverse_spatial_scale,hgrad]
  have he(i j:Fin 3):r⁻¹^2*inverseSpatial z i j*
      inner ℝ (scalarGradient z i) (scalarGradient z j)=
      r⁻¹^2*(inverseSpatial z i j*
        inner ℝ (scalarGradient z i) (scalarGradient z j)):=by ring
  simp only [he,←Finset.mul_sum]
  field_simp [hr]
theorem scalar_spatial_complete_current:
    SourceClockPhiMatchedDiffusionSource.completeCurrent scalarSpatialAction=
      (12:ℂ) • (U*scalarSpatialAction):=by
  have he:scalarSpatialAction=multiply spatialValue spatial_smooth:=rfl
  rw [he]
  have hD:deltaPhi (multiply spatialValue spatial_smooth)-
      deltaGauge (multiply spatialValue spatial_smooth)=(-0:ℂ) •
        (multiply spatialValue spatial_smooth):=by
    rw [←he,SourceScalarVirialBulk.original_signed_spatial_phi,
      SourceScalarVirialBulk.original_signed_spatial_gauge]
    module
  have hScale:scaleDerivative (multiply spatialValue spatial_smooth)=
      (3*(2/3:ℂ)-1) • multiply spatialValue spatial_smooth:=by
    have h:=scale_real_degree spatialValue spatial_smooth 1 spatial_coframe
    convert h using 1
    norm_num
  have h:=complete_current_real_multiplier spatialValue spatial_smooth (2/3) 0 hD hScale
  simpa only [show (0:ℂ)*0-3*0+18*(2/3)=12 by norm_num] using h

private theorem magnetic_smooth(z:physicalChart):ContDiffAt ℝ ∞ magneticPotential z.val:=by
  exact (volume_smooth.contDiffAt.div_const _).mul
    (ContDiffAt.sum (fun i _=>ContDiffAt.sum (fun j _=>
      (inverseSpatial_smooth i j z).mul
        ((magneticField_smooth i).contDiffAt.inner ℝ (magneticField_smooth j).contDiffAt))))
private theorem magnetic_coframe(r:ℝ)(z:SourceCoordinateSlice)(hr:r≠0):
    magneticPotential (SourceCoframeVolume.scale r z)=r^(1:ℤ)*magneticPotential z:=by
  have hmag(i:Fin 3):magneticField (SourceCoframeVolume.scale r z) i=magneticField z i:=rfl
  simp only [magneticPotential,volume_scale,inverse_spatial_scale,hmag]
  have he(i j:Fin 3):r⁻¹^2*inverseSpatial z i j*
      inner ℝ (magneticField z i) (magneticField z j)=
      r⁻¹^2*(inverseSpatial z i j*
        inner ℝ (magneticField z i) (magneticField z j)):=by ring
  simp only [he,←Finset.mul_sum]
  field_simp [hr]
theorem magnetic_complete_current:
    SourceClockPhiMatchedDiffusionSource.completeCurrent magneticAction=
      (16:ℂ) • (U*magneticAction):=by
  have he:magneticAction=multiply magneticPotential magnetic_smooth:=rfl
  rw [he]
  have hD:deltaPhi (multiply magneticPotential magnetic_smooth)-
      deltaGauge (multiply magneticPotential magnetic_smooth)=(-4:ℂ) •
        (multiply magneticPotential magnetic_smooth):=by
    rw [←he,SourceScalarVirialBulk.original_magnetic_phi,
      SourceScalarVirialBulk.original_magnetic_gauge]
    module
  have hScale:scaleDerivative (multiply magneticPotential magnetic_smooth)=
      (3*(2/3:ℂ)-1) • multiply magneticPotential magnetic_smooth:=by
    have h:=scale_real_degree magneticPotential magnetic_smooth 1 magnetic_coframe
    convert h using 1
    norm_num
  have h:=complete_current_real_multiplier magneticPotential magnetic_smooth (2/3) 4 hD hScale
  simpa only [show (4:ℂ)*4-3*4+18*(2/3)=16 by norm_num] using h

end LowEnergy.SourceClockPhiOriginalGaussianH0RealPrimitives
