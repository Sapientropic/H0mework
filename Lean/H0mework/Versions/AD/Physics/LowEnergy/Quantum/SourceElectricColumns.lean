import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceGaugeRadialPair

/-! The actual thirty-six P286 covariant columns contract with the source radial gradient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceElectricColumns
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussHistoryHilbert GaussLiveMomentum
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumResidualGaugeSlice SourceQuantumFockGauge
open SourceGaugeRadius SourceGaugeRadiusMetric SourceGaugeRadialCurrent SourceGaugeRadialPair
open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace Matrix
abbrev CoreEnd := QuantumTest →ₗ[ℂ] QuantumTest

def logGauge (z : SourceCoordinateSlice) : Gauge :=
  radialWeight z • spatialMap (electricKernel z) (z.2.2 : Gauge)

def logCoefficient (i : Fin 3) (a : LieIndex) (z : SourceCoordinateSlice) : ℝ :=
  ⟪lieBasis a,gaugeCoordinates (logGauge z) i⟫

def radialCoefficient (i : Fin 3) (a : LieIndex) (z : SourceCoordinateSlice) : ℝ :=
  radialWeight z*⟪lieBasis a,connectionField z i⟫

theorem log_gauge_gradient (z : SourceCoordinateSlice) :
    logGauge z=(radialWeight z/2) • electricGradient z := by
  rw [electric_gradient_kernel]
  unfold logGauge
  rw [smul_smul]
  congr 1
  ring

theorem metric_log_gauge (z : physicalChart) :
    electricMetric z.val (logGauge z.val)=radialWeight z.val • (z.val.2.2 : Gauge) := by
  unfold electricMetric logGauge
  rw [map_smul, ←spatial_map_mul, metric_kernel, spatial_map_one]

theorem log_gauge_square (z : physicalChart) :
    ⟪logGauge z.val,electricMetric z.val (logGauge z.val)⟫=radialWeight z.val := by
  rw [log_gauge_gradient, map_smul, real_inner_smul_left, real_inner_smul_right,
    metric_gradient_square]
  unfold radialWeight
  field_simp [(electric_square_pos z).ne']
  ring

theorem log_coefficient_formula (i : Fin 3) (a : LieIndex) (z : SourceCoordinateSlice) :
    logCoefficient i a z=radialWeight z*∑ j : Fin 3,
      electricKernel z i j*⟪lieBasis a,connectionField z j⟫ := by
  unfold logCoefficient logGauge
  change ⟪lieBasis a,radialWeight z • gaugeCoordinates (spatialMap (electricKernel z) (z.2.2 : Gauge)) i⟫=_
  rw [real_inner_smul_right, spatial_map_apply, inner_sum]
  simp only [real_inner_smul_right]
  rfl

private theorem kernel_smooth (i j : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => electricKernel w i j) z.val := by
  have ht (k l : Fin 3) : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => triad w.1 k l) := by
    fin_cases k
    · fin_cases l
      · change ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => w.1 0)
        fun_prop
      · exact contDiff_const
      · exact contDiff_const
    · fin_cases l
      · change ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => w.1 1)
        fun_prop
      · change ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => w.1 2)
        fun_prop
      · exact contDiff_const
    · fin_cases l
      · change ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => w.1 3)
        fun_prop
      · change ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => w.1 4)
        fun_prop
      · change ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => w.1 5)
        fun_prop
  have hc : ContDiffAt ℝ ∞ (fun w => sourceTime 0/(sourceSigma*volume w)) z.val :=
    contDiffAt_const.div (contDiffAt_const.mul volume_smooth.contDiffAt)
      (mul_ne_zero source_sigma_nonzero (volume_pos z).ne')
  change ContDiffAt ℝ ∞ (fun w => (sourceTime 0/(sourceSigma*volume w))*
    ∑ k : Fin 3, triad w.1 k i*triad w.1 k j) z.val
  exact hc.mul (ContDiffAt.sum (fun k _ => (ht k i).contDiffAt.mul (ht k j).contDiffAt))

theorem log_coefficient_smooth (i : Fin 3) (a : LieIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (logCoefficient i a) z.val := by
  have he : logCoefficient i a=(fun w => radialWeight w*∑ j : Fin 3,
      electricKernel w i j*⟪lieBasis a,connectionField w j⟫) := funext (log_coefficient_formula i a)
  rw [he]
  exact (radial_weight_smooth z).mul (ContDiffAt.sum (fun j _ =>
    (kernel_smooth i j z).mul (contDiffAt_const.inner ℝ (connectionField_smooth j).contDiffAt)))

theorem radial_coefficient_smooth (i : Fin 3) (a : LieIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (radialCoefficient i a) z.val :=
  (radial_weight_smooth z).mul (contDiffAt_const.inner ℝ (connectionField_smooth i).contDiffAt)

theorem metric_log_coefficient (z : SourceCoordinateSlice) (i : Fin 3) (a : LieIndex) :
    (∑ j : Fin 3, gaugeWeight z i j*logCoefficient j a z)=
      ⟪lieBasis a,gaugeCoordinates (electricMetric z (logGauge z)) i⟫ := by
  change _=⟪lieBasis a,gaugeCoordinates (spatialMap (Matrix.of (gaugeWeight z)) (logGauge z)) i⟫
  rw [spatial_map_apply, inner_sum]
  simp only [real_inner_smul_right]
  rfl

theorem metric_log_radial (z : physicalChart) (i : Fin 3) (a : LieIndex) :
    (∑ j : Fin 3, gaugeWeight z.val i j*logCoefficient j a z.val)=radialCoefficient i a z.val := by
  rw [metric_log_coefficient, metric_log_gauge]
  change ⟪lieBasis a,radialWeight z.val • gaugeCoordinates (z.val.2.2 : Gauge) i⟫=_
  rw [real_inner_smul_right]
  rfl

private theorem gauge_basis_pair (A B : Gauge) :
    (∑ a : LieIndex, ∑ i : Fin 3,
      ⟪lieBasis a,gaugeCoordinates A i⟫*⟪lieBasis a,gaugeCoordinates B i⟫)=⟪A,B⟫ := by
  rw [Finset.sum_comm]
  change (∑ i : Fin 3, ∑ a : LieIndex,
    ⟪lieBasis a,gaugeCoordinates A i⟫*⟪lieBasis a,gaugeCoordinates B i⟫)=
      ∑ i : Fin 3, ⟪gaugeCoordinates A i,gaugeCoordinates B i⟫
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ a : LieIndex, ⟪gaugeCoordinates A i,lieBasis a⟫*⟪lieBasis a,gaugeCoordinates B i⟫ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [real_inner_comm (lieBasis a) (gaugeCoordinates A i)]
    _ = _ := lieBasis.sum_inner_mul_inner _ _

theorem log_coefficient_square (z : physicalChart) :
    (∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
      logCoefficient i a z.val*(gaugeWeight z.val i j*logCoefficient j a z.val))=radialWeight z.val := by
  simp_rw [←Finset.mul_sum, metric_log_coefficient]
  change (∑ a : LieIndex, ∑ i : Fin 3,
    ⟪lieBasis a,gaugeCoordinates (logGauge z.val) i⟫*
      ⟪lieBasis a,gaugeCoordinates (electricMetric z.val (logGauge z.val)) i⟫)=_
  rw [gauge_basis_pair, log_gauge_square]

def column (i : Fin 3) (a : LieIndex) : CoreEnd := covariantMomentum (gaugeDirection i a)
def logColumn (i : Fin 3) (a : LieIndex) : CoreEnd :=
  multiply (logCoefficient i a) (log_coefficient_smooth i a)
def radialColumn (i : Fin 3) (a : LieIndex) : CoreEnd :=
  multiply (radialCoefficient i a) (radial_coefficient_smooth i a)
def metricColumn (i j : Fin 3) : CoreEnd :=
  multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)

theorem metric_log_columns (i : Fin 3) (a : LieIndex) :
    (∑ j : Fin 3, metricColumn i j*logColumn j a)=radialColumn i a := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (∑ j : Fin 3, (gaugeWeight z i j : ℂ)*((logCoefficient j a z : ℂ)*f z word))=
    (radialCoefficient i a z : ℂ)*f z word
  by_cases hz : z ∈ physicalChart
  · have h := metric_log_radial ⟨z,hz⟩ i a
    have hc : (∑ j : Fin 3, (gaugeWeight z i j : ℂ)*(logCoefficient j a z : ℂ))=
        (radialCoefficient i a z : ℂ) := by exact_mod_cast h
    simp_rw [←mul_assoc]
    rw [←Finset.sum_mul, hc]
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp [hf]

private def gaugeInsert (i : Fin 3) : NativeLie →ₗ[ℝ] Ambient :=
  (0 : NativeLie →ₗ[ℝ] Scalar).prod
    ((WithLp.linearEquiv 2 ℝ (Fin 3 → NativeLie)).symm.toLinearMap.comp
      (LinearMap.single ℝ (fun _ : Fin 3 => NativeLie) i))

private theorem gauge_insert_coordinates (i j : Fin 3) (x : NativeLie) :
    gaugeCoordinates (gaugeInsert i x).2 j=if j=i then x else 0 := by
  change (Pi.single i x : Fin 3 → NativeLie) j=if j=i then x else 0
  simp only [Pi.single_apply]

theorem gauge_direction_expansion (A : Gauge) :
    (∑ a : LieIndex, ∑ i : Fin 3,
      ⟪lieBasis a,gaugeCoordinates A i⟫ • gaugeDirection i a)=((0 : Scalar),A) := by
  have hi (i : Fin 3) : (∑ a : LieIndex,
      ⟪lieBasis a,gaugeCoordinates A i⟫ • gaugeDirection i a)=gaugeInsert i (gaugeCoordinates A i) := by
    change (∑ a : LieIndex, ⟪lieBasis a,gaugeCoordinates A i⟫ • gaugeInsert i (lieBasis a))=_
    simp only [←map_smul]
    rw [←map_sum, lieBasis.sum_repr']
  rw [Finset.sum_comm]
  simp_rw [hi]
  apply Prod.ext
  · simp [gaugeInsert, Prod.fst_sum]
  · apply gaugeCoordinates.injective
    funext i
    simp only [Prod.snd_sum, map_sum, Finset.sum_apply, gauge_insert_coordinates]
    simp

def pointMomentum (f : QuantumTest) (z : SourceCoordinateSlice) : Ambient →ₗ[ℝ] FockFiber where
  toFun v := covariantMomentum v f z
  map_add' v w := by
    simp only [covariantMomentum_apply, map_add, Prod.fst_add, Prod.snd_add]
    rw [show ((0 : Coframe),(inverseL z v).2+(inverseL z w).2)=
      (0,(inverseL z v).2)+(0,(inverseL z w).2) by simp, map_add]
    simp only [add_apply, smul_add]
    abel
  map_smul' r v := by
    simp only [covariantMomentum_apply, map_smul, Prod.smul_fst, Prod.smul_snd]
    rw [show ((0 : Coframe),r • (inverseL z v).2)=r • (0,(inverseL z v).2) by simp, map_smul]
    simp only [smul_apply, ←smul_add]
    rw [smul_comm (-Complex.I) r]
    rfl

theorem radial_direction_expansion (z : physicalChart) :
    (∑ a : LieIndex, ∑ i : Fin 3, radialCoefficient i a z.val • gaugeDirection i a)=radialAmbient z.val := by
  unfold radialCoefficient
  simp only [mul_smul, ←Finset.smul_sum]
  change radialWeight z.val • (∑ a : LieIndex, ∑ i : Fin 3,
    ⟪lieBasis a,gaugeCoordinates (z.val.2.2 : Gauge) i⟫ • gaugeDirection i a)=_
  rw [gauge_direction_expansion]
  unfold radialAmbient
  rw [metric_gradient]
  change radialWeight z.val • ((0 : Scalar),(z.val.2.2 : Gauge))=
    (radialWeight z.val/2) • ((0 : Scalar),(2 : ℝ) • (z.val.2.2 : Gauge))
  simp only [Prod.smul_mk, smul_zero, smul_smul]
  have hc : radialWeight z.val/2*2=radialWeight z.val := by ring
  rw [hc]

private def evaluate (z : SourceCoordinateSlice) : QuantumTest →ₗ[ℂ] FockFiber where
  toFun f := f z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem radial_column_contraction (f : QuantumTest) :
    (∑ a : LieIndex, ∑ i : Fin 3, radialColumn i a (column i a f))=(-Complex.I) • radialAction f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have he := congrArg (pointMomentum f z) (radial_direction_expansion ⟨z,hz⟩)
    simp only [map_sum, map_smul] at he
    have hreal (a : LieIndex) (i : Fin 3) : radialColumn i a (column i a f) z=
        radialCoefficient i a z • pointMomentum f z (gaugeDirection i a) := by
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    have hev : (∑ a : LieIndex, ∑ i : Fin 3, radialColumn i a (column i a f)) z=
        ∑ a : LieIndex, ∑ i : Fin 3, radialCoefficient i a z • pointMomentum f z (gaugeDirection i a) := by
      change evaluate z (∑ a : LieIndex, ∑ i : Fin 3, radialColumn i a (column i a f))=_
      simp only [map_sum]
      change (∑ a : LieIndex, ∑ i : Fin 3, radialColumn i a (column i a f) z)=_
      simp_rw [hreal]
    rw [hev, he]
    exact original_native_radial_current f ⟨z,hz⟩
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz
      ((∑ a : LieIndex, ∑ i : Fin 3, radialColumn i a (column i a f)).tsupport_subset h)),
      image_eq_zero_of_notMem_tsupport (fun h => hz (((-Complex.I) • radialAction f).tsupport_subset h))]

end LowEnergy.SourceElectricColumns
