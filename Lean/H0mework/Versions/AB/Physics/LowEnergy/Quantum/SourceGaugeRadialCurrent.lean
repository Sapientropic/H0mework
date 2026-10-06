import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceGaugeRadiusMetric

/-! The original gauge radius and Number density generate one radial current field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceGaugeRadialCurrent
open SaturationMonoid.PhysicsCore
open StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumResidualGaugeSlice
open SourceQuantumGaugeSliceCoordinates SourceQuantumScalarOrbitDimensions SourceQuantumFockGauge SourceQuantumResidualFlow
open GaussHistoryHilbert GaussDensityCore GaussLiveMomentum GaussCoreDifferential
open GaussNativeEnergy GaussNativePotential SourceCornerWeight SourceGaugeRadius SourceGaugeRadiusMetric
open scoped ContDiff Topology RealInnerProductSpace

private def orbitScale (r : ℝ) : Module.End ℝ (stabilizer × coordinateSlice) :=
  (r • (LinearMap.id : stabilizer →ₗ[ℝ] stabilizer)).prodMap LinearMap.id

private theorem relative_scale (r : ℝ) (A : Gauge) :
    relative (r • A)=(relative A).comp (orbitScale r) := by
  have h : combined (r • A)=(combined A).comp (orbitScale r) := by
    apply LinearMap.ext
    rintro ⟨a,v⟩
    change gaugeAction a (r • A)+(v : Gauge)=gaugeAction (r • a) A+(v : Gauge)
    simp only [map_smul, LinearMap.smul_apply]
  rw [relative, h]
  rfl

theorem jacobian_scale (r : ℝ) (A : Gauge) : jacobian (r • A)=|r|^3*jacobian A := by
  have hd : (orbitScale r).det=r^3 := by
    rw [orbitScale, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id,
      LinearMap.det_id, stabilizer_finrank]
    ring
  have hm : (relativeMatrix (r • A)).det=(relativeMatrix A).det*r^3 := by
    simp only [relativeMatrix, LinearMap.det_toMatrix]
    rw [relative_scale, LinearMap.det_comp, hd]
  rw [jacobian, hm, abs_mul, abs_pow, jacobian]
  ring

def gaugeScale (r : ℝ) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  (z.1,z.2.1,r • z.2.2)

def gaugeEuler (z : SourceCoordinateSlice) : SourceCoordinateSlice := (0,0,z.2.2)

theorem gauge_scale_one (z : SourceCoordinateSlice) : gaugeScale 1 z=z := by simp [gaugeScale]

theorem gauge_scale_derivative (z : SourceCoordinateSlice) (r : ℝ) :
    HasDerivAt (fun s => gaugeScale s z) (gaugeEuler z) r := by
  have h := (hasDerivAt_const r z.1).prodMk
    ((hasDerivAt_const r z.2.1).prodMk ((hasDerivAt_id r).smul_const z.2.2))
  simpa only [gaugeScale, gaugeEuler, id_eq, one_smul] using! h

theorem density_scale (N : ℕ) (r : ℝ) (z : SourceCoordinateSlice) :
    density N (gaugeScale r z)=|r|^3*density N z := by
  change jacobian (r • (z.2.2 : Gauge))*(z.1 0*z.1 2*z.1 5)^(N+2)=_
  rw [jacobian_scale]
  unfold density
  ring

theorem density_euler (N : ℕ) (z : physicalChart) :
    fderiv ℝ (density N) z.val (gaugeEuler z.val)=3*density N z.val := by
  have chain := ((density_smooth N z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (gauge_scale_derivative z.val 1) (gauge_scale_one z.val).symm
  have actual : HasDerivAt (fun r => density N (gaugeScale r z.val)) (3*density N z.val) 1 := by
    have generated := ((hasDerivAt_id (1 : ℝ)).pow 3).mul_const (density N z.val)
    have hp : HasDerivAt (fun r : ℝ => r^3*density N z.val) (3*density N z.val) 1 := by
      simpa only [id_eq, Pi.pow_apply, one_pow, mul_one, Nat.cast_ofNat, Nat.reduceSub] using! generated
    apply hp.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds (show (0 : ℝ)<1 by norm_num)] with r hr
    rw [density_scale, abs_of_pos hr]
  exact chain.unique actual

theorem complex_density_euler (N : ℕ) (z : physicalChart) :
    fderiv ℝ (complexDensity N) z.val (gaugeEuler z.val)=3*complexDensity N z.val := by
  have h := (Complex.ofRealCLM.hasFDerivAt (x := density N z.val)).comp z.val
    ((density_smooth N z).differentiableAt (by simp)).hasFDerivAt
  change HasFDerivAt (complexDensity N) _ z.val at h
  rw [h.fderiv]
  change (fderiv ℝ (density N) z.val (gaugeEuler z.val) : ℂ)=_
  rw [density_euler]
  push_cast
  rfl

theorem gauge_square_pos (z : physicalChart) : 0<gaugeSquare z.val := by
  have hA : connectionField z.val 0 ≠ 0 := by
    intro he
    have hf := congrArg (fun A : NativeLie => (SourceQuantumNativeDimensions.nativeCoordinates A).1 1) he
    change firstGauge (z.val.2.2 : Gauge)=
      (SourceQuantumNativeDimensions.nativeCoordinates 0).1 1 at hf
    simp only [map_zero] at hf
    exact (ne_of_gt z.property.2.2.2.2.1) hf
  have hrow : gaugeRow z.val 0 ≠ 0 := by
    simpa only [gaugeRow, Matrix.cons_val_zero] using smul_ne_zero (ne_of_gt z.property.1) hA
  have hi : 0 < inner ℝ (gaugeRow z.val 0) (gaugeRow z.val 0) := real_inner_self_pos.mpr hrow
  exact hi.trans_le (Finset.single_le_sum (fun i _ => real_inner_self_nonneg)
    (Finset.mem_univ (0 : Fin 3)))

theorem gauge_square_smooth : ContDiff ℝ ∞ gaugeSquare := by
  have hr (i : Fin 3) : ContDiff ℝ ∞ (fun z => gaugeRow z i) := by
    have h0 := connectionField_smooth 0
    have h1 := connectionField_smooth 1
    have h2 := connectionField_smooth 2
    fin_cases i <;> dsimp [gaugeRow] <;> fun_prop
  exact ContDiff.sum (fun i _ => ContDiff.inner ℝ (hr i) (hr i))

theorem electric_square_pos (z : physicalChart) : 0<electricSquare z.val := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact Stage9C.Material.SpinPair.lapse_pos
  have hs : 0<sourceSigma := positiveSmoothUnifiedSource.legacy.sigma_pos
  exact mul_pos (div_pos hn (mul_pos hs (volume_pos z))) (gauge_square_pos z)

theorem electric_square_smooth (z : physicalChart) : ContDiffAt ℝ ∞ electricSquare z.val :=
  ((contDiffAt_const.div (contDiffAt_const.mul volume_smooth.contDiffAt)
    (mul_ne_zero source_sigma_nonzero (volume_pos z).ne')).mul gauge_square_smooth.contDiffAt)

private theorem gauge_row_scale (r : ℝ) (z : SourceCoordinateSlice) (i : Fin 3) :
    gaugeRow (gaugeScale r z) i=r • gaugeRow z i := by
  rw [←gauge_row_map]
  change gaugeRowMap z.1 i (r • (z.2.2 : Gauge))=r • gaugeRow z i
  rw [map_smul, gauge_row_map]

theorem electric_square_scale (r : ℝ) (z : SourceCoordinateSlice) :
    electricSquare (gaugeScale r z)=r^2*electricSquare z := by
  unfold electricSquare gaugeSquare
  change (sourceTime 0/(sourceSigma*volume z))*
    (∑ i : Fin 3, inner ℝ (gaugeRow (gaugeScale r z) i) (gaugeRow (gaugeScale r z) i)) = _
  simp only [gauge_row_scale, real_inner_smul_left, real_inner_smul_right]
  simp_rw [←mul_assoc]
  rw [←Finset.mul_sum]
  ring

theorem electric_square_euler (z : physicalChart) :
    fderiv ℝ electricSquare z.val (gaugeEuler z.val)=2*electricSquare z.val := by
  have chain := ((electric_square_smooth z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (gauge_scale_derivative z.val 1) (gauge_scale_one z.val).symm
  have actual : HasDerivAt (fun r => electricSquare (gaugeScale r z.val))
      (2*electricSquare z.val) 1 := by
    simpa only [electric_square_scale, id_eq, Pi.pow_apply, one_pow, mul_one,
      Nat.cast_ofNat, Nat.reduceSub] using
      ((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (electricSquare z.val)
  exact chain.unique actual

def radialWeight (z : SourceCoordinateSlice) : ℝ := (electricSquare z)⁻¹

theorem radial_weight_smooth (z : physicalChart) : ContDiffAt ℝ ∞ radialWeight z.val :=
  (electric_square_smooth z).inv (electric_square_pos z).ne'

theorem radial_weight_euler (z : physicalChart) :
    fderiv ℝ radialWeight z.val (gaugeEuler z.val)= -2*radialWeight z.val := by
  have h := (hasDerivAt_inv (electric_square_pos z).ne').comp_hasFDerivAt z.val
    ((electric_square_smooth z).differentiableAt (by simp)).hasFDerivAt
  change HasFDerivAt radialWeight _ z.val at h
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [electric_square_euler]
  unfold radialWeight
  field_simp [(electric_square_pos z).ne']

def radialAmbient (z : SourceCoordinateSlice) : Ambient :=
  (radialWeight z/2) • (0,electricMetric z (electricGradient z))

theorem radial_native_direction (z : physicalChart) :
    direction (radialAmbient z.val) z.val=radialWeight z.val • gaugeEuler z.val := by
  unfold direction radialAmbient
  rw [map_smul, inverse_metric_gradient]
  change (0,(radialWeight z.val/2) • (0,(2 : ℝ) • z.val.2.2)) =
    radialWeight z.val • (0,0,z.val.2.2)
  simp only [Prod.smul_mk, smul_zero, smul_smul]
  have hc : radialWeight z.val/2*2=radialWeight z.val := by ring
  rw [hc]

theorem radial_connection_zero (z : physicalChart) : connection (radialAmbient z.val) z.val=0 := by
  have hc := metric_gradient_connection_zero z
  unfold connection at hc ⊢
  unfold radialAmbient
  rw [map_smul]
  change GaussNativeMatter.nativeFock ((radialWeight z.val/2) •
    (inverseL z.val (0,electricMetric z.val (electricGradient z.val))).1)=0
  rw [map_smul, hc]
  apply ContinuousLinearMap.ext
  intro psi
  apply PiLp.ext
  intro word
  change (radialWeight z.val/2 : ℝ) • (0 : ℂ)=0
  simp only [Complex.real_smul, mul_zero]

end LowEnergy.SourceGaugeRadialCurrent
