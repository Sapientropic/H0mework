import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussMomentumAdjoint
import H0mework.Physics.Exterior.GlobalIntegratedAction

/-! Native scalar/gauge energy coefficients at the original source time column. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SaturationMonoid.PhysicsCore
open StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource
open scoped ContDiff Matrix

abbrev Spatial := Fin 3

def sourceSigma : ℝ := Stage9C.Material.SpinPair.sourceCoupling

def sourceTime : Fin 4 → ℝ := fun i => Stage9C.Material.SpinPair.actual.coframe 0 i 0

theorem source_time_generated : sourceTime = ![Stage9C.Material.SpinPair.lapse, 0, 0, 0] := by
  funext i
  fin_cases i <;> rfl

theorem source_sigma_generated : sourceSigma =
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).strongCouplingSquared := rfl

theorem source_common_coupling :
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).strongCouplingSquared =
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).weakCouplingSquared ∧
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).strongCouplingSquared =
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).hyperchargeCouplingSquared := ⟨rfl,rfl⟩

def triad (q : Coframe) : Matrix Spatial Spatial ℝ :=
  !![q 0, 0, 0; q 1, q 2, 0; q 3, q 4, q 5]

def coframe (time : Fin 4 → ℝ) (q : Coframe) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![time 0, 0, 0, 0; time 1, q 0, 0, 0; time 2, q 1, q 2, 0; time 3, q 3, q 4, q 5]

def triadInverse (q : Coframe) : Matrix Spatial Spatial ℝ :=
  !![(q 0)⁻¹, 0, 0;
    -(q 1)/(q 0*q 2), (q 2)⁻¹, 0;
    (q 1*q 4-q 2*q 3)/(q 0*q 2*q 5), -(q 4)/(q 2*q 5), (q 5)⁻¹]

theorem triad_inverse_right (z : physicalChart) : triad z.val.1 * triadInverse z.val.1 = 1 := by
  have h0 := (ne_of_gt z.property.1)
  have h2 := (ne_of_gt z.property.2.1)
  have h5 := (ne_of_gt z.property.2.2.1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triad, triadInverse, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

theorem triad_inverse_left (z : physicalChart) : triadInverse z.val.1 * triad z.val.1 = 1 := by
  have h0 := (ne_of_gt z.property.1)
  have h2 := (ne_of_gt z.property.2.1)
  have h5 := (ne_of_gt z.property.2.2.1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triad, triadInverse, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

def volume (z : SourceCoordinateSlice) : ℝ := z.1 0*z.1 2*z.1 5

def inverseSpatial (z : SourceCoordinateSlice) : Matrix Spatial Spatial ℝ :=
  triadInverse z.1 * (triadInverse z.1).transpose

def scalarWeight (z : SourceCoordinateSlice) : ℝ := -sourceTime 0 / volume z

def gaugeWeight (z : SourceCoordinateSlice) (i j : Spatial) : ℝ :=
  (sourceSigma * volume z / sourceTime 0) * inverseSpatial z i j

theorem gaugeWeight_symmetric (z : SourceCoordinateSlice) (i j : Spatial) :
    gaugeWeight z i j = gaugeWeight z j i := by
  unfold gaugeWeight inverseSpatial
  congr 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem volume_pos (z : physicalChart) : 0 < volume z.val :=
  GaussHistoryHilbert.spatialVolume_pos z

theorem volume_smooth : ContDiff ℝ ∞ volume := by unfold volume; fun_prop

theorem scalarWeight_smooth (z : physicalChart) : ContDiffAt ℝ ∞ scalarWeight z.val :=
  contDiffAt_const.div volume_smooth.contDiffAt (volume_pos z).ne'

theorem triadInverse_smooth (i j : Spatial) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => triadInverse w.1 i j) z.val := by
  have h0 := (ne_of_gt z.property.1)
  have h2 := (ne_of_gt z.property.2.1)
  have h5 := (ne_of_gt z.property.2.2.1)
  have h02 : z.val.1 0 * z.val.1 2 ≠ 0 := mul_ne_zero h0 h2
  have h25 : z.val.1 2 * z.val.1 5 ≠ 0 := mul_ne_zero h2 h5
  have h025 : z.val.1 0 * z.val.1 2 * z.val.1 5 ≠ 0 := mul_ne_zero h02 h5
  have hq (k : Fin 6) : ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => w.1 k) z.val := by fun_prop
  fin_cases i
  · fin_cases j
    · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => (w.1 0)⁻¹) z.val
      exact (hq 0).inv h0
    · exact contDiffAt_const
    · exact contDiffAt_const
  · fin_cases j
    · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -(w.1 1)/(w.1 0*w.1 2)) z.val
      exact (hq 1).neg.div ((hq 0).mul (hq 2)) h02
    · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => (w.1 2)⁻¹) z.val
      exact (hq 2).inv h2
    · exact contDiffAt_const
  · fin_cases j
    · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice =>
        (w.1 1*w.1 4-w.1 2*w.1 3)/(w.1 0*w.1 2*w.1 5)) z.val
      exact (((hq 1).mul (hq 4)).sub ((hq 2).mul (hq 3))).div
        (((hq 0).mul (hq 2)).mul (hq 5)) h025
    · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => -(w.1 4)/(w.1 2*w.1 5)) z.val
      exact (hq 4).neg.div ((hq 2).mul (hq 5)) h25
    · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => (w.1 5)⁻¹) z.val
      exact (hq 5).inv h5

theorem gaugeWeight_smooth (i j : Spatial) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => gaugeWeight w i j) z.val := by
  have hi : ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => inverseSpatial w i j) z.val := by
    simp only [inverseSpatial, Matrix.mul_apply, Matrix.transpose_apply]
    exact ContDiffAt.sum (fun k _ => (triadInverse_smooth i k z).mul (triadInverse_smooth j k z))
  exact ((contDiffAt_const.mul volume_smooth.contDiffAt).div_const _).mul hi

def sourceBFKernel (time : Fin 4 → ℝ) (q : Coframe) (i j : Fin 6) : ℝ :=
  -coframeTwoFormMetricPairing (coframe time q) (Pi.single i 1) (Pi.single j 1) /
    (sourceSigma * (coframe time q).det)

theorem coframe_determinant (time : Fin 4 → ℝ) (q : Coframe) :
    (coframe time q).det = time 0 * (q 0*q 2*q 5) := by
  have h : (coframe time q).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> simp [coframe] at hij ⊢
  rw [Matrix.det_of_isLowerTriangular _ h]
  simp [coframe, Fin.prod_univ_four]
  ring

theorem sourceBFKernel_wedge (time : Fin 4 → ℝ) (q : Coframe) (i j : Fin 6) :
    sourceBFKernel time q i j =
      -(∑ p : Fin 6, lorentzianTwoFormSign p *
        ProofFreeRicherAnholonomicSource.coframeWedge (coframe time q) p i *
        ProofFreeRicherAnholonomicSource.coframeWedge (coframe time q) p j) /
        (sourceSigma*(coframe time q).det) := by
  simp [sourceBFKernel, coframeTwoFormMetricPairing, coframeTwoFormLinear,
    Pi.single_apply, mul_ite]

def electricKernel (z : SourceCoordinateSlice) : Matrix Spatial Spatial ℝ :=
  (sourceTime 0/(sourceSigma*volume z)) • ((triad z.1).transpose * triad z.1)

theorem source_electric_kernel (z : physicalChart) (i j : Spatial) :
    sourceBFKernel sourceTime z.val.1 (Fin.castAdd 3 i) (Fin.castAdd 3 j) = electricKernel z.val i j := by
  have hn : sourceTime 0 ≠ 0 := by
    rw [source_time_generated]
    exact Stage9C.Material.SpinPair.lapse_pos.ne'
  rw [sourceBFKernel_wedge, coframe_determinant]
  fin_cases i <;> fin_cases j <;>
    simp [ProofFreeRicherAnholonomicSource.coframeWedge,
      ProofFreeRicherAnholonomicSource.pairFirst, ProofFreeRicherAnholonomicSource.pairSecond,
      lorentzianTwoFormSign, coframe, source_time_generated, electricKernel, triad,
      Fin.sum_univ_six, Fin.sum_univ_three, Matrix.mul_apply, volume] <;>
    field_simp <;> ring

theorem source_time_nonzero : sourceTime 0 ≠ 0 := by
  rw [source_time_generated]
  exact Stage9C.Material.SpinPair.lapse_pos.ne'

theorem source_sigma_nonzero : sourceSigma ≠ 0 := by
  exact ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos

theorem gaugeWeight_inverse (z : physicalChart) :
    (electricKernel z.val)⁻¹ = gaugeWeight z.val := by
  apply Matrix.inv_eq_right_inv (A := electricKernel z.val)
    (B := (gaugeWeight z.val : Matrix Spatial Spatial ℝ))
  have hn := source_time_nonzero
  have hs := source_sigma_nonzero
  have h0 := (ne_of_gt z.property.1)
  have h2 := (ne_of_gt z.property.2.1)
  have h5 := (ne_of_gt z.property.2.2.1)
  ext i j
  change (∑ k : Spatial, electricKernel z.val i k * gaugeWeight z.val k j) =
    if i = j then 1 else 0
  simp only [electricKernel, Matrix.smul_apply, gaugeWeight,
    inverseSpatial, Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [triad, triadInverse, Fin.sum_univ_three, volume] <;>
    field_simp <;> ring

theorem source_electric_magnetic_zero (z : SourceCoordinateSlice) (i j : Spatial) :
    sourceBFKernel sourceTime z.1 (Fin.castAdd 3 i) (Fin.natAdd 3 j) = 0 := by
  rw [sourceBFKernel_wedge]
  fin_cases i <;> fin_cases j <;>
    simp [ProofFreeRicherAnholonomicSource.coframeWedge,
      ProofFreeRicherAnholonomicSource.pairFirst, ProofFreeRicherAnholonomicSource.pairSecond,
      lorentzianTwoFormSign, coframe, source_time_generated, Fin.sum_univ_six]

theorem source_magnetic_kernel (z : physicalChart) (i j : Spatial) :
    sourceBFKernel sourceTime z.val.1 (Fin.natAdd 3 i) (Fin.natAdd 3 j) =
      -(volume z.val/(sourceSigma*sourceTime 0))*inverseSpatial z.val i j := by
  have hn := source_time_nonzero
  have hs := source_sigma_nonzero
  have h0 := (ne_of_gt z.property.1)
  have h2 := (ne_of_gt z.property.2.1)
  have h5 := (ne_of_gt z.property.2.2.1)
  rw [sourceBFKernel_wedge, coframe_determinant]
  fin_cases i <;> fin_cases j <;>
    simp [ProofFreeRicherAnholonomicSource.coframeWedge,
      ProofFreeRicherAnholonomicSource.pairFirst, ProofFreeRicherAnholonomicSource.pairSecond,
      lorentzianTwoFormSign, coframe, source_time_generated, inverseSpatial, triadInverse,
      Fin.sum_univ_six, Fin.sum_univ_three, Matrix.mul_apply, volume] <;>
    field_simp <;> ring

def coframeInverse (q : Coframe) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(sourceTime 0)⁻¹,0,0,0;
      0,triadInverse q 0 0,triadInverse q 0 1,triadInverse q 0 2;
      0,triadInverse q 1 0,triadInverse q 1 1,triadInverse q 1 2;
      0,triadInverse q 2 0,triadInverse q 2 1,triadInverse q 2 2]

theorem coframe_inverse (z : physicalChart) :
    (coframe sourceTime z.val.1)⁻¹ = coframeInverse z.val.1 := by
  apply Matrix.inv_eq_right_inv (A := coframe sourceTime z.val.1)
    (B := coframeInverse z.val.1)
  have hn := Stage9C.Material.SpinPair.lapse_pos.ne'
  have h0 := (ne_of_gt z.property.1)
  have h2 := (ne_of_gt z.property.2.1)
  have h5 := (ne_of_gt z.property.2.2.1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coframe, coframeInverse, triadInverse, source_time_generated,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp <;> ring

def scalarMetric (z : SourceCoordinateSlice) : Matrix (Fin 4) (Fin 4) ℝ :=
  (coframe sourceTime z.1).det • (lorentzianMetricOfCoframe (coframe sourceTime z.1))⁻¹

private theorem minkowski_inverse : minkowskiInternalMetric⁻¹ = minkowskiInternalMetric := by
  apply Matrix.inv_eq_right_inv (A := minkowskiInternalMetric) (B := minkowskiInternalMetric)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minkowskiInternalMetric, Matrix.mul_apply, Fin.sum_univ_four]

theorem scalarMetric_formula (z : physicalChart) :
    scalarMetric z.val = (sourceTime 0*volume z.val) •
      (coframeInverse z.val.1 * minkowskiInternalMetric * (coframeInverse z.val.1).transpose) := by
  simp only [scalarMetric, lorentzianMetricOfCoframe, Matrix.mul_inv_rev,
    ← Matrix.transpose_nonsing_inv, minkowski_inverse, coframe_inverse,
    coframe_determinant, volume, Matrix.mul_assoc]

theorem source_scalar_temporal (z : physicalChart) :
    scalarMetric z.val 0 0 = -volume z.val/sourceTime 0 := by
  rw [scalarMetric_formula]
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply]
  simp [coframeInverse, minkowskiInternalMetric, Fin.sum_univ_four]
  field_simp

theorem source_scalar_weight (z : physicalChart) :
    (scalarMetric z.val 0 0)⁻¹ = scalarWeight z.val := by
  rw [source_scalar_temporal]
  simp [scalarWeight, neg_div]

theorem source_scalar_mixed (z : physicalChart) (i : Spatial) :
    scalarMetric z.val 0 (Fin.succ i) = 0 := by
  rw [scalarMetric_formula]
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases i <;>
    simp [coframeInverse, minkowskiInternalMetric, Fin.sum_univ_four]

theorem source_scalar_spatial (z : physicalChart) (i j : Spatial) :
    scalarMetric z.val (Fin.succ i) (Fin.succ j) =
      sourceTime 0*volume z.val*inverseSpatial z.val i j := by
  rw [scalarMetric_formula]
  simp only [Matrix.smul_apply, inverseSpatial, Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [coframeInverse, minkowskiInternalMetric, Fin.sum_univ_four, Fin.sum_univ_three]

#print axioms source_time_generated
#print axioms source_sigma_generated
#print axioms triad_inverse_right
#print axioms scalarWeight_smooth
#print axioms gaugeWeight_smooth
#print axioms source_electric_kernel
#print axioms gaugeWeight_inverse
#print axioms source_magnetic_kernel
#print axioms source_scalar_weight
#print axioms source_scalar_spatial
end LowEnergy.GaussNativeEnergy
