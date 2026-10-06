import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussCoreHilbert
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussDensityCore
open GaussHistoryHilbert GaussLiveMomentum
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open MeasureTheory Set Function
open scoped ContDiff Distributions Topology ENNReal

abbrev ScalarTest := 𝓓(physicalChart, ℂ)

theorem relative_det_smooth : ContDiff ℝ ∞ (fun A : Gauge => (relativeMatrix A).det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro sigma _
  exact contDiff_const.mul (contDiff_prod (fun i _ => relativeMatrix_smooth (sigma i) i))

theorem jacobian_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ jacobian (z.val.2.2 : Gauge) := by
  have hd : (relativeMatrix (z.val.2.2 : Gauge)).det ≠ 0 := by
    simpa only [relativeMatrix, LinearMap.det_toMatrix] using residual_relative_det z
  exact contDiffAt_const.mul (relative_det_smooth.contDiffAt.abs hd)

def density (N : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  jacobian (z.2.2 : Gauge) * (z.1 0 * z.1 2 * z.1 5) ^ (N+2)

theorem density_on_chart (N : ℕ) (z : physicalChart) : density N z.val = GaussHistoryHilbert.numberWeight N z := rfl

theorem density_pos (N : ℕ) (z : physicalChart) : 0 < density N z.val := GaussHistoryHilbert.numberWeight_pos N z

theorem density_smooth (N : ℕ) (z : physicalChart) : ContDiffAt ℝ ∞ (density N) z.val := by
  have hg : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => (w.2.2 : Gauge)) :=
    coordinateSlice.subtypeL.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have hv : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => w.1 0 * w.1 2 * w.1 5) := by fun_prop
  exact ((jacobian_smooth z).comp z.val hg.contDiffAt).mul (hv.pow _).contDiffAt

def complexDensity (N : ℕ) (z : SourceCoordinateSlice) : ℂ := density N z

theorem complexDensity_smooth (N : ℕ) (z : physicalChart) :
    ContDiffAt ℝ ∞ (complexDensity N) z.val :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (density_smooth N z)

theorem inverseDensity_smooth (N : ℕ) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => (complexDensity N w)⁻¹) z.val := by
  apply (complexDensity_smooth N z).inv
  change (density N z.val : ℂ) ≠ 0
  exact_mod_cast (density_pos N z).ne'

def multiplyValue (w : SourceCoordinateSlice → ℂ) (f : ScalarTest)
    (z : SourceCoordinateSlice) : ℂ := w z * f z

theorem multiply_support (w : SourceCoordinateSlice → ℂ) (f : ScalarTest) :
    tsupport (multiplyValue w f) ⊆ tsupport f := tsupport_mul_subset_right

theorem multiply_smooth (w : SourceCoordinateSlice → ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ w z.val) (f : ScalarTest) :
    ContDiff ℝ ∞ (multiplyValue w f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · exact (smooth ⟨z, f.tsupport_subset hz⟩).mul f.contDiff.contDiffAt
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [isClosed_tsupport f |>.isOpen_compl.mem_nhds hz] with x hx
    simp [multiplyValue, image_eq_zero_of_notMem_tsupport hx]

def multiply (w : SourceCoordinateSlice → ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ w z.val) : ScalarTest →ₗ[ℂ] ScalarTest where
  toFun f := ⟨multiplyValue w f, multiply_smooth w smooth f,
    f.hasCompactSupport.of_isClosed_subset isClosed_closure (multiply_support w f),
    (multiply_support w f).trans f.tsupport_subset⟩
  map_add' f g := by
    apply DFunLike.ext
    intro z
    exact mul_add (w z) (f z) (g z)
  map_smul' c f := by
    apply DFunLike.ext
    intro z
    change w z * (c * f z) = c * (w z * f z)
    ring

def derivative (v : SourceCoordinateSlice) : ScalarTest →ₗ[ℂ] ScalarTest :=
  (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v).toLinearMap

def weightedTranspose (N : ℕ) (v : SourceCoordinateSlice) : ScalarTest →ₗ[ℂ] ScalarTest :=
  -((multiply (fun z => (complexDensity N z)⁻¹) (inverseDensity_smooth N)).comp
    ((derivative v).comp (multiply (complexDensity N) (complexDensity_smooth N))))

theorem weightedTranspose_apply (N : ℕ) (v : SourceCoordinateSlice) (f : ScalarTest)
    (z : physicalChart) :
    weightedTranspose N v f z.val = -(complexDensity N z.val)⁻¹ *
      fderiv ℝ (fun w => complexDensity N w * f w) z.val v := by
  change -((complexDensity N z.val)⁻¹ *
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v
      (multiply (complexDensity N) (complexDensity_smooth N) f) z.val) = _
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le (𝕜 := ℂ) (n := ⊤) (k := ⊤) _ (by simp), neg_mul]
  rfl

instance configuration_haar : GaussHistoryHilbert.configurationMeasure.IsAddHaarMeasure := by
  have : coframeMeasure.IsAddHaarMeasure := by unfold coframeMeasure; infer_instance
  have : SourceQuantumScalarHilbert.sliceMeasure.IsAddHaarMeasure := by
    unfold SourceQuantumScalarHilbert.sliceMeasure
    infer_instance
  have : GaussHistoryHilbert.coordinateGaugeMeasure.IsAddHaarMeasure := by
    unfold GaussHistoryHilbert.coordinateGaugeMeasure
    infer_instance
  have : IsLocallyFiniteMeasure SourceQuantumScalarHilbert.sliceMeasure := by
    unfold SourceQuantumScalarHilbert.sliceMeasure
    infer_instance
  have : (SourceQuantumScalarHilbert.sliceMeasure.prod
      GaussHistoryHilbert.coordinateGaugeMeasure).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure SourceQuantumScalarHilbert.sliceMeasure
      GaussHistoryHilbert.coordinateGaugeMeasure
  exact Measure.prod.instIsAddHaarMeasure coframeMeasure
    (SourceQuantumScalarHilbert.sliceMeasure.prod GaussHistoryHilbert.coordinateGaugeMeasure)

theorem derivative_apply (v : SourceCoordinateSlice) (f : ScalarTest) (z : SourceCoordinateSlice) :
    derivative v f z = fderiv ℝ f z v := by
  change TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v f z = _
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le (𝕜 := ℂ) (n := ⊤) (k := ⊤) f (by simp)]

def conjugate (f : ScalarTest) : ScalarTest :=
  TestFunction.postcompCLM (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap f

theorem conjugate_apply (f : ScalarTest) (z : SourceCoordinateSlice) : conjugate f z = star (f z) := rfl

theorem derivative_conjugate (v : SourceCoordinateSlice) (f : ScalarTest) (z : SourceCoordinateSlice) :
    derivative v (conjugate f) z = star (derivative v f z) := by
  let C := (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z)
  have hh := C.hasFDerivAt.comp z hf
  rw [derivative_apply, derivative_apply]
  change fderiv ℝ (C ∘ f) z v = C (fderiv ℝ f z v)
  rw [hh.fderiv]
  rfl

theorem product_integration_by_parts (v : SourceCoordinateSlice) (f g : ScalarTest) :
    (∫ z, f z * derivative v g z ∂GaussHistoryHilbert.configurationMeasure) =
      -(∫ z, derivative v f z * g z ∂GaussHistoryHilbert.configurationMeasure) := by
  let B := ContinuousLinearMap.mul ℝ ℂ
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (B := B)
  · exact ((derivative v f).continuous.mul g.continuous).integrable_of_hasCompactSupport
      (g.hasCompactSupport.mul_left)
  · exact (f.continuous.mul (derivative v g).continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.mul_right)
  · exact (f.continuous.mul g.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.mul_right)
  · intro z _
    rw [derivative_apply]
    exact ((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).hasLineDerivAt v
  · intro z _
    rw [derivative_apply]
    exact ((g.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).hasLineDerivAt v

theorem density_transpose_cancel (N : ℕ) (v : SourceCoordinateSlice) (f : ScalarTest)
    (z : SourceCoordinateSlice) :
    complexDensity N z * weightedTranspose N v f z =
      -derivative v (multiply (complexDensity N) (complexDensity_smooth N) f) z := by
  by_cases hz : z ∈ physicalChart
  · have hn : complexDensity N z ≠ 0 := by
      change (density N z : ℂ) ≠ 0
      exact_mod_cast (density_pos N ⟨z,hz⟩).ne'
    change complexDensity N z * (-((complexDensity N z)⁻¹ * _)) = _
    field_simp
    rfl
  · have hf : weightedTranspose N v f z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((weightedTranspose N v f).tsupport_subset h))
    have hg : derivative v (multiply (complexDensity N) (complexDensity_smooth N) f) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz
        ((derivative v (multiply (complexDensity N) (complexDensity_smooth N) f)).tsupport_subset h))
    rw [hf, hg, mul_zero, neg_zero]

def pair (N : ℕ) (f g : ScalarTest) : ℂ :=
  ∫ z, complexDensity N z * star (f z) * g z ∂GaussHistoryHilbert.configurationMeasure

theorem weighted_transpose_pair (N : ℕ) (v : SourceCoordinateSlice) (f g : ScalarTest) :
    pair N f (derivative v g) = pair N (weightedTranspose N v f) g := by
  have h := product_integration_by_parts v
    (conjugate (multiply (complexDensity N) (complexDensity_smooth N) f)) g
  have hc (z : SourceCoordinateSlice) := congrArg star (density_transpose_cancel N v f z)
  have hs (z : SourceCoordinateSlice) : star (complexDensity N z) = complexDensity N z := by
    simp [complexDensity]
  simp only [star_mul, hs, star_neg] at hc
  change (∫ z, complexDensity N z * star (f z) * derivative v g z
      ∂GaussHistoryHilbert.configurationMeasure) = _
  calc
    _ = -(∫ z, star (derivative v (multiply (complexDensity N) (complexDensity_smooth N) f) z) * g z
        ∂GaussHistoryHilbert.configurationMeasure) := by
      have hm (x : SourceCoordinateSlice) :
          conjugate (multiply (complexDensity N) (complexDensity_smooth N) f) x =
            complexDensity N x * star (f x) := by
        change star (complexDensity N x * f x) = _
        rw [star_mul, hs, mul_comm]
      calc
        _ = (∫ z, conjugate (multiply (complexDensity N) (complexDensity_smooth N) f) z *
              derivative v g z ∂GaussHistoryHilbert.configurationMeasure) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun z =>
            congrArg (fun c : ℂ => c * derivative v g z) (hm z).symm)
        _ = _ := h
        _ = _ := by
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun z =>
            congrArg (fun c : ℂ => c * g z)
              (derivative_conjugate v (multiply (complexDensity N) (complexDensity_smooth N) f) z))
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        change -(star (derivative v (multiply (complexDensity N) (complexDensity_smooth N) f) z) * g z) =
          complexDensity N z * star (weightedTranspose N v f z) * g z
        rw [mul_comm (complexDensity N z), hc z, neg_mul])

theorem hilbert_pair (N : ℕ) (f g : ScalarTest) :
    inner ℂ (GaussCoreHilbert.scalarLp N f) (GaussCoreHilbert.scalarLp N g) = pair N f g := by
  rw [L2.inner_def]
  calc
    _ = ∫ z : physicalChart, star (f z) * g z ∂GaussHistoryHilbert.numberMeasure N := by
      apply integral_congr_ae
      filter_upwards [GaussCoreHilbert.scalarLp_ae N f, GaussCoreHilbert.scalarLp_ae N g] with z hf hg
      simp only [hf, hg, RCLike.inner_apply]
      exact mul_comm _ _
    _ = ∫ z : physicalChart, (ENNReal.ofReal (GaussHistoryHilbert.numberWeight N z)).toReal • (star (f z) * g z)
        ∂GaussHistoryHilbert.chartMeasure := by
      exact integral_withDensity_eq_integral_toReal_smul
        (ENNReal.continuous_ofReal.comp (GaussHistoryHilbert.numberWeight_continuous N)).measurable
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _
    _ = ∫ z : physicalChart, complexDensity N z.val * star (f z) * g z ∂GaussHistoryHilbert.chartMeasure := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun z => ?_)
      change (ENNReal.ofReal (GaussHistoryHilbert.numberWeight N z)).toReal • (star (f z) * g z) =
        complexDensity N z.val * star (f z) * g z
      rw [ENNReal.toReal_ofReal (GaussHistoryHilbert.numberWeight_pos N z).le, RCLike.real_smul_eq_coe_mul]
      change (complexDensity N z.val) * (star (f z) * g z) = _
      rw [mul_assoc]
    _ = ∫ z in (physicalChart : Set SourceCoordinateSlice),
        complexDensity N z * star (f z) * g z ∂GaussHistoryHilbert.configurationMeasure :=
      integral_subtype_comap (μ := GaussHistoryHilbert.configurationMeasure) (G := ℂ)
        physicalChart.isOpen.measurableSet (fun z => complexDensity N z * star (f z) * g z)
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h)), star_zero,
        mul_zero, zero_mul]

theorem weighted_transpose_hilbert (N : ℕ) (v : SourceCoordinateSlice) (f g : ScalarTest) :
    inner ℂ (GaussCoreHilbert.scalarLp N f) (GaussCoreHilbert.scalarLp N (derivative v g)) =
      inner ℂ (GaussCoreHilbert.scalarLp N (weightedTranspose N v f)) (GaussCoreHilbert.scalarLp N g) := by
  rw [hilbert_pair, hilbert_pair, weighted_transpose_pair]

#print axioms density_smooth
#print axioms weightedTranspose
#print axioms weightedTranspose_apply
#print axioms weighted_transpose_pair
#print axioms weighted_transpose_hilbert
end LowEnergy.GaussDensityCore
