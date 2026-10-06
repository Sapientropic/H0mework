import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussDensityCore

/-! The original residual-orbit determinant pays the gauge-density derivative.
The scaling is an actual configuration variation, not a selected quantum state. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace LowEnergy.ActualGaugeMeasure
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates
open SourceQuantumResidualFlow SourceQuantumScalarOrbitDimensions
open GaussHistoryHilbert GaussDensityCore
open scoped Topology ContDiff

def orbitScale (r : ℝ) : Module.End ℝ (stabilizer × coordinateSlice) :=
  (r • (LinearMap.id : stabilizer →ₗ[ℝ] stabilizer)).prodMap LinearMap.id

theorem combined_smul (r : ℝ) (A : Gauge) :
    combined (r • A)=(combined A).comp (orbitScale r) := by
  apply LinearMap.ext
  rintro ⟨a,v⟩
  change gaugeAction a (r • A)+(v : Gauge)=gaugeAction (r • a) A+(v : Gauge)
  simp only [map_smul,LinearMap.smul_apply]

theorem relative_smul (r : ℝ) (A : Gauge) :
    relative (r • A)=(relative A).comp (orbitScale r) := by
  rw [relative,combined_smul]
  rfl

theorem orbitScale_det (r : ℝ) : (orbitScale r).det=r^3 := by
  rw [orbitScale,LinearMap.det_prodMap,LinearMap.det_smul,LinearMap.det_id,
    LinearMap.det_id,stabilizer_finrank]
  ring

theorem relativeMatrix_smul_det (r : ℝ) (A : Gauge) :
    (relativeMatrix (r • A)).det=(relativeMatrix A).det*r^3 := by
  simp only [relativeMatrix,LinearMap.det_toMatrix]
  rw [relative_smul,LinearMap.det_comp,orbitScale_det]

theorem jacobian_smul (r : ℝ) (A : Gauge) :
    jacobian (r • A)=|r|^3*jacobian A := by
  rw [jacobian,relativeMatrix_smul_det,abs_mul,abs_pow,jacobian]
  ring

def scale (r : ℝ) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  (z.1,z.2.1,r • z.2.2)

theorem density_scale (N : ℕ) (r : ℝ) (z : SourceCoordinateSlice) :
    density N (scale r z)=|r|^3*density N z := by
  change jacobian (r • (z.2.2 : Gauge))*(z.1 0*z.1 2*z.1 5)^(N+2)=_
  rw [jacobian_smul]
  unfold density
  ring

theorem density_scale_positive (N : ℕ) (r : ℝ) (positive : 0<r)
    (z : SourceCoordinateSlice) : density N (scale r z)=r^3*density N z := by
  rw [density_scale,abs_of_pos positive]

theorem scale_mem (r : ℝ) (positive : 0<r) (z : physicalChart) :
    scale r z.val ∈ physicalChart := by
  refine ⟨z.property.1,z.property.2.1,z.property.2.2.1,z.property.2.2.2.1,?_,?_,?_⟩
  · change 0<firstGauge (r • (z.val.2.2 : Gauge))
    rw [map_smul,smul_eq_mul]
    exact mul_pos positive z.property.2.2.2.2.1
  · change 0<secondGauge (r • (z.val.2.2 : Gauge))
    rw [map_smul,smul_eq_mul]
    exact mul_pos positive z.property.2.2.2.2.2.1
  · change 0<jacobian (r • (z.val.2.2 : Gauge))
    rw [jacobian_smul,abs_of_pos positive]
    exact mul_pos (pow_pos positive _) z.property.2.2.2.2.2.2

theorem density_scale_derivative (N : ℕ) (z : SourceCoordinateSlice)
    (r : ℝ) (positive : 0<r) :
    HasDerivAt (fun s => density N (scale s z)) (3*r^2*density N z) r := by
  have generated := ((hasDerivAt_id r).pow 3).mul_const (density N z)
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,mul_one] at generated
  apply generated.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds positive] with s hs
  exact density_scale_positive N s hs z

theorem source_density_scale (N : ℕ) (r : ℝ) :
    density N (scale r GaussHistoryHilbert.sourcePoint.val)=|r|^3*sourceJacobian := by
  rw [density_scale]
  change |r|^3*GaussHistoryHilbert.numberWeight N GaussHistoryHilbert.sourcePoint=_
  rw [source_weight]

theorem source_density_scale_derivative (N : ℕ) :
    HasDerivAt (fun s => density N (scale s GaussHistoryHilbert.sourcePoint.val))
      (3*sourceJacobian) 1 := by
  have h := density_scale_derivative N GaussHistoryHilbert.sourcePoint.val 1 (by norm_num)
  change HasDerivAt _ (3*1^2*GaussHistoryHilbert.numberWeight N GaussHistoryHilbert.sourcePoint) 1 at h
  simpa only [source_weight,one_pow,mul_one] using h

def euler (z : SourceCoordinateSlice) : SourceCoordinateSlice := (0,0,z.2.2)

theorem scale_one (z : SourceCoordinateSlice) : scale 1 z=z := by
  simp only [scale,one_smul]

theorem scale_derivative (z : SourceCoordinateSlice) (r : ℝ) :
    HasDerivAt (fun s => scale s z) (euler z) r := by
  have h := (hasDerivAt_const r z.1).prodMk
    ((hasDerivAt_const r z.2.1).prodMk ((hasDerivAt_id r).smul_const z.2.2))
  simpa only [scale,euler,id_eq,one_smul] using! h

theorem density_euler (N : ℕ) (z : physicalChart) :
    fderiv ℝ (density N) z.val (euler z.val)=3*density N z.val := by
  have chain := ((density_smooth N z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (scale_derivative z.val 1) (scale_one z.val).symm
  have actual := density_scale_derivative N z.val 1 (by norm_num)
  have same := chain.unique actual
  simpa only [one_pow,mul_one] using same

theorem complexDensity_euler (N : ℕ) (z : physicalChart) :
    fderiv ℝ (complexDensity N) z.val (euler z.val)=3*complexDensity N z.val := by
  have chain := ((complexDensity_smooth N z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (scale_derivative z.val 1) (scale_one z.val).symm
  have actual := (density_scale_derivative N z.val 1 (by norm_num)).ofReal_comp
  have same := chain.unique actual
  simpa only [one_pow,mul_one,Complex.ofReal_mul,Complex.ofReal_ofNat,complexDensity] using same

/-- The direction is frozen at z; this is not the adjoint of the Euler field. -/
theorem frozen_euler_weightedTranspose (N : ℕ) (z : physicalChart)
    (r : ℝ) (f : ScalarTest) :
    weightedTranspose N (r • euler z.val) f z.val=
      -fderiv ℝ f z.val (r • euler z.val)-(3*(r : ℂ))*f z.val := by
  rw [weightedTranspose_apply]
  have hd := ((complexDensity_smooth N z).differentiableAt (by simp)).hasFDerivAt
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have product : fderiv ℝ (fun w => complexDensity N w*f w) z.val=
      complexDensity N z.val • fderiv ℝ f z.val+f z.val • fderiv ℝ (complexDensity N) z.val := by
    simpa using! (hd.mul hf).fderiv
  rw [product]
  simp only [add_apply,smul_apply,smul_eq_mul]
  have hdir : fderiv ℝ (complexDensity N) z.val (r • euler z.val)=
      (3*(r : ℂ))*complexDensity N z.val := by
    rw [map_smul,complexDensity_euler]
    change (r : ℂ)*(3*complexDensity N z.val)=_
    ring
  rw [hdir]
  have nonzero : complexDensity N z.val≠0 := by
    change (density N z.val : ℂ)≠0
    exact_mod_cast (density_pos N z).ne'
  field_simp [nonzero]
  ring

theorem source_weightedTranspose (N : ℕ) (r : ℝ) (f : ScalarTest) :
    weightedTranspose N (r • euler GaussHistoryHilbert.sourcePoint.val) f
        GaussHistoryHilbert.sourcePoint.val=
      -fderiv ℝ f GaussHistoryHilbert.sourcePoint.val
        (r • euler GaussHistoryHilbert.sourcePoint.val)-
      (3*(r : ℂ))*f GaussHistoryHilbert.sourcePoint.val :=
  frozen_euler_weightedTranspose N GaussHistoryHilbert.sourcePoint r f

end LowEnergy.ActualGaugeMeasure
