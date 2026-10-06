import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceGaugeRadius

/-! The literal source electric metric returns the original gauge radial vector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceGaugeRadiusMetric
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumResidualGaugeSlice GaussLiveMomentum GaussHistoryHilbert
open GaussNativeEnergy SourceCornerWeight SourceGaugeRadius
open scoped ContDiff Topology RealInnerProductSpace Matrix

def spatialLinear (M : Matrix (Fin 3) (Fin 3) ℝ) : Gauge →ₗ[ℝ] Gauge where
  toFun A := WithLp.toLp 2 (fun i => ∑ j : Fin 3, M i j • gaugeCoordinates A j)
  map_add' A B := by
    apply gaugeCoordinates.injective
    funext i
    change (∑ j : Fin 3, M i j • (gaugeCoordinates A j+gaugeCoordinates B j)) =
      (∑ j : Fin 3, M i j • gaugeCoordinates A j)+(∑ j : Fin 3, M i j • gaugeCoordinates B j)
    simp only [smul_add, Finset.sum_add_distrib]
  map_smul' r A := by
    apply gaugeCoordinates.injective
    funext i
    change (∑ j : Fin 3, M i j • (r • gaugeCoordinates A j)) =
      r • ∑ j : Fin 3, M i j • gaugeCoordinates A j
    simp only [smul_comm (M _ _) r, Finset.smul_sum]

def spatialMap (M : Matrix (Fin 3) (Fin 3) ℝ) : Gauge →L[ℝ] Gauge :=
  (spatialLinear M).toContinuousLinearMap

theorem spatial_map_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (A : Gauge) (i : Fin 3) :
    gaugeCoordinates (spatialMap M A) i=∑ j : Fin 3, M i j • gaugeCoordinates A j := rfl

theorem spatial_map_mul (M N : Matrix (Fin 3) (Fin 3) ℝ) (A : Gauge) :
    spatialMap (M*N) A=spatialMap M (spatialMap N A) := by
  apply gaugeCoordinates.injective
  funext i
  simp only [spatial_map_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]

theorem spatial_map_one (A : Gauge) : spatialMap 1 A=A := by
  apply gaugeCoordinates.injective
  funext i
  simp [spatial_map_apply, Matrix.one_apply]

theorem spatial_map_smul (r : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (A : Gauge) :
    spatialMap (r • M) A=r • spatialMap M A := by
  apply gaugeCoordinates.injective
  funext i
  change (∑ j : Fin 3, (r*M i j) • gaugeCoordinates A j) =
    r • ∑ j : Fin 3, M i j • gaugeCoordinates A j
  simp only [mul_smul, Finset.smul_sum]

theorem spatial_transpose_pair (M : Matrix (Fin 3) (Fin 3) ℝ) (A B : Gauge) :
    ⟪spatialMap M.transpose A,B⟫=⟪A,spatialMap M B⟫ := by
  change (∑ i : Fin 3, ⟪∑ j : Fin 3, M j i • gaugeCoordinates A j,gaugeCoordinates B i⟫) =
    ∑ j : Fin 3, ⟪gaugeCoordinates A j,∑ i : Fin 3, M j i • gaugeCoordinates B i⟫
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]

private theorem spatial_triad_row (z : SourceCoordinateSlice) (A : Gauge) (i : Fin 3) :
    gaugeCoordinates (spatialMap (triad z.1) A) i=gaugeRowMap z.1 i A := by
  simp only [spatial_map_apply, gaugeRowMap, sum_apply, smul_apply]
  rfl

theorem gauge_gradient_matrix (z : SourceCoordinateSlice) :
    gaugeGradient z=(2 : ℝ) • spatialMap ((triad z.1).transpose*triad z.1) (z.2.2 : Gauge) := by
  apply ext_inner_right ℝ
  intro B
  rw [gauge_gradient_pair, real_inner_smul_left, spatial_map_mul, spatial_transpose_pair]
  change 2*(∑ i : Fin 3, ⟪gaugeRow z i,gaugeRowMap z.1 i B⟫) =
    2*(∑ i : Fin 3, ⟪gaugeCoordinates (spatialMap (triad z.1) (z.2.2 : Gauge)) i,
      gaugeCoordinates (spatialMap (triad z.1) B) i⟫)
  simp only [spatial_triad_row, gauge_row_map]

def electricMetric (z : SourceCoordinateSlice) : Gauge →L[ℝ] Gauge :=
  spatialMap (Matrix.of (gaugeWeight z))

def electricSquare (z : SourceCoordinateSlice) : ℝ :=
  (sourceTime 0/(sourceSigma*volume z))*gaugeSquare z

def electricGradient (z : SourceCoordinateSlice) : Gauge :=
  (sourceTime 0/(sourceSigma*volume z)) • gaugeGradient z

theorem electric_square_derivative (z : SourceCoordinateSlice) (v : Gauge) :
    fderiv ℝ (fun A : Gauge => (sourceTime 0/(sourceSigma*volume z))*ambientGaugeSquare z.1 A)
      (z.2.2 : Gauge) v=⟪electricGradient z,v⟫ := by
  have hd : DifferentiableAt ℝ (ambientGaugeSquare z.1) (z.2.2 : Gauge) := by
    unfold ambientGaugeSquare
    exact DifferentiableAt.fun_sum (fun i _ =>
      (gaugeRowMap z.1 i).differentiableAt.inner ℝ (gaugeRowMap z.1 i).differentiableAt)
  rw [fderiv_const_mul hd, smul_apply, smul_eq_mul, gauge_square_derivative]
  exact (real_inner_smul_left _ _ _).symm

theorem electric_gradient_kernel (z : SourceCoordinateSlice) :
    electricGradient z=(2 : ℝ) • spatialMap (electricKernel z) (z.2.2 : Gauge) := by
  rw [electricGradient, gauge_gradient_matrix]
  unfold electricKernel
  rw [spatial_map_smul]
  module

theorem metric_kernel (z : physicalChart) :
    Matrix.of (gaugeWeight z.val)*electricKernel z.val=1 := by
  change (((sourceSigma*volume z.val/sourceTime 0) •
      (triadInverse z.val.1*(triadInverse z.val.1).transpose)) *
      ((sourceTime 0/(sourceSigma*volume z.val)) • ((triad z.val.1).transpose*triad z.val.1)))=1
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hc : (sourceSigma*volume z.val/sourceTime 0)*
      (sourceTime 0/(sourceSigma*volume z.val))=1 := by
    field_simp [source_time_nonzero, source_sigma_nonzero, (volume_pos z).ne']
  rw [hc, one_smul]
  calc
    _ = triadInverse z.val.1*((triadInverse z.val.1).transpose*(triad z.val.1).transpose)*
        triad z.val.1 := by noncomm_ring
    _ = triadInverse z.val.1*((triad z.val.1*triadInverse z.val.1).transpose)*
        triad z.val.1 := by rw [Matrix.transpose_mul]
    _ = 1 := by rw [triad_inverse_right z, Matrix.transpose_one, mul_one, triad_inverse_left z]

theorem metric_gradient (z : physicalChart) :
    electricMetric z.val (electricGradient z.val)=(2 : ℝ) • (z.val.2.2 : Gauge) := by
  rw [electric_gradient_kernel, map_smul]
  change (2 : ℝ) • spatialMap (Matrix.of (gaugeWeight z.val))
    (spatialMap (electricKernel z.val) (z.val.2.2 : Gauge)) = _
  rw [←spatial_map_mul, metric_kernel, spatial_map_one]

theorem metric_gradient_square (z : physicalChart) :
    ⟪electricGradient z.val,electricMetric z.val (electricGradient z.val)⟫=4*electricSquare z.val := by
  rw [metric_gradient, electricGradient, real_inner_smul_left, real_inner_smul_right,
    gauge_gradient_euler, electricSquare]
  ring

theorem inverse_metric_gradient (z : physicalChart) :
    inverseL z.val (0,electricMetric z.val (electricGradient z.val))=
      (0,(0,(2 : ℝ) • z.val.2.2)) := by
  rw [metric_gradient]
  have h : ((0 : Scalar),(2 : ℝ) • (z.val.2.2 : Gauge))=
      (2 : ℝ) • ((0 : Scalar),(z.val.2.2 : Gauge)) := by simp
  rw [h, map_smul, inverse_gauge_euler]
  simp

theorem metric_gradient_connection_zero (z : physicalChart) :
    GaussCoreDifferential.connection (0,electricMetric z.val (electricGradient z.val)) z.val=0 := by
  unfold GaussCoreDifferential.connection
  rw [inverse_metric_gradient]
  exact map_zero GaussNativeMatter.nativeFock

theorem metric_gradient_native_direction (z : physicalChart) :
    GaussCoreDifferential.direction (0,electricMetric z.val (electricGradient z.val)) z.val=
      (0,(0,(2 : ℝ) • z.val.2.2)) := by
  unfold GaussCoreDifferential.direction
  rw [inverse_metric_gradient]

end LowEnergy.SourceGaugeRadiusMetric
