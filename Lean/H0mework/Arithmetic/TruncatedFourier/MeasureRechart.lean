import H0mework.Arithmetic.TruncatedFourier.RadiusActualBridge
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Pointwise

noncomputable section

abbrev BurnolUnitIntervalL2 := BurnolRadiusIntervalL2 1

def burnolRadiusScale (radius : ℝ) : ℝ → ℝ := fun x ↦ radius * x

theorem burnolRadiusScale_preimage_interval
    {radius : ℝ} (positive : 0 < radius) :
    burnolRadiusScale radius ⁻¹' symmetricInterval radius =
      symmetricInterval 1 := by
  ext x
  simp only [burnolRadiusScale, symmetricInterval, mem_preimage, mem_Icc]
  constructor <;> rintro ⟨left, right⟩ <;> constructor <;> nlinarith

def burnolRadiusScaledRestrictedMeasure (radius : ℝ) : Measure ℝ :=
  ENNReal.ofReal radius⁻¹ •
    ((volume : Measure ℝ).restrict (symmetricInterval radius))

theorem burnolRadiusScale_map_restricted
    {radius : ℝ} (positive : 0 < radius) :
    Measure.map (burnolRadiusScale radius)
        ((volume : Measure ℝ).restrict (symmetricInterval 1)) =
      burnolRadiusScaledRestrictedMeasure radius := by
  have measurable : Measurable (burnolRadiusScale radius) := by
    change Measurable (fun x : ℝ ↦ radius * x)
    fun_prop
  calc
    _ = Measure.map (burnolRadiusScale radius)
        ((volume : Measure ℝ).restrict
          (burnolRadiusScale radius ⁻¹' symmetricInterval radius)) := by
      rw [burnolRadiusScale_preimage_interval positive]
    _ = (Measure.map (burnolRadiusScale radius) (volume : Measure ℝ)).restrict
        (symmetricInterval radius) :=
      (Measure.restrict_map measurable
        (measurableSet_symmetricInterval radius)).symm
    _ = (ENNReal.ofReal |radius⁻¹| • (volume : Measure ℝ)).restrict
        (symmetricInterval radius) := by
      change (Measure.map (radius * ·) (volume : Measure ℝ)).restrict
        (symmetricInterval radius) = _
      rw [Real.map_volume_mul_left positive.ne']
    _ = _ := by
      rw [Measure.restrict_smul, abs_of_pos (inv_pos.mpr positive)]
      rfl

theorem burnolRadiusScaleMeasurePreserving
    {radius : ℝ} (positive : 0 < radius) :
    MeasurePreserving (burnolRadiusScale radius)
      ((volume : Measure ℝ).restrict (symmetricInterval 1))
      (burnolRadiusScaledRestrictedMeasure radius) where
  measurable := by
    change Measurable (fun x : ℝ ↦ radius * x)
    fun_prop
  map_eq := burnolRadiusScale_map_restricted positive

theorem burnolRadiusScaledRestrictedMeasure_factor_ne_zero
    {radius : ℝ} (positive : 0 < radius) :
    ENNReal.ofReal radius⁻¹ ≠ 0 := by
  exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr positive)

theorem burnolRadiusScaledRestrictedMeasure_factor_ne_top
    (radius : ℝ) : ENNReal.ofReal radius⁻¹ ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem burnolRadiusState_memLp_scaledMeasure
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) :
    MemLp (state : ℝ → ℂ) 2 (burnolRadiusScaledRestrictedMeasure radius) := by
  unfold burnolRadiusScaledRestrictedMeasure
  exact (Lp.memLp state).smul_measure ENNReal.ofReal_ne_top

def burnolRadiusStateInScaledMeasure
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) :
    Lp ℂ 2 (burnolRadiusScaledRestrictedMeasure radius) :=
  (burnolRadiusState_memLp_scaledMeasure state).toLp state

theorem burnolRadiusStateInScaledMeasure_coe
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) :
    burnolRadiusStateInScaledMeasure state =ᵐ[burnolRadiusScaledRestrictedMeasure radius]
      (state : ℝ → ℂ) :=
  MemLp.coeFn_toLp (burnolRadiusState_memLp_scaledMeasure state)

theorem burnolRadiusStateInScaledMeasure_norm
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolRadiusIntervalL2 radius) :
    ‖burnolRadiusStateInScaledMeasure state‖ =
      Real.sqrt radius⁻¹ * ‖state‖ := by
  rw [burnolRadiusStateInScaledMeasure, Lp.norm_toLp,
    toReal_eLpNorm
      (burnolRadiusState_memLp_scaledMeasure state).aestronglyMeasurable]
  unfold burnolRadiusScaledRestrictedMeasure
  change lpNorm (state : ℝ → ℂ) 2
      (Real.toNNReal radius⁻¹ •
        ((volume : Measure ℝ).restrict (symmetricInterval radius))) = _
  rw [lpNorm_smul_measure_of_ne_zero
    (show Real.toNNReal radius⁻¹ ≠ 0 by
      exact ne_of_gt (Real.toNNReal_pos.mpr (inv_pos.mpr positive)))]
  simp only [NNReal.smul_def]
  rw [show ((2 : ℝ≥0∞).toReal⁻¹) = (1 / 2 : ℝ) by norm_num]
  rw [NNReal.coe_rpow]
  rw [Real.coe_toNNReal _ (inv_pos.mpr positive).le]
  rw [← Real.sqrt_eq_rpow]
  simp only [smul_eq_mul]
  rw [← toReal_eLpNorm (Lp.memLp state).aestronglyMeasurable]
  rw [← Lp.norm_def]

theorem burnolRadiusStateInScaledMeasure_add
    {radius : ℝ} (left right : BurnolRadiusIntervalL2 radius) :
    burnolRadiusStateInScaledMeasure (left + right) =
      burnolRadiusStateInScaledMeasure left +
        burnolRadiusStateInScaledMeasure right := by
  apply Lp.ext
  have sourceRead := Measure.ae_smul_measure (Lp.coeFn_add left right)
    (ENNReal.ofReal radius⁻¹)
  filter_upwards [
    burnolRadiusStateInScaledMeasure_coe (left + right),
    burnolRadiusStateInScaledMeasure_coe left,
    burnolRadiusStateInScaledMeasure_coe right,
    sourceRead,
    Lp.coeFn_add (burnolRadiusStateInScaledMeasure left)
      (burnolRadiusStateInScaledMeasure right)]
      with x sumRead leftRead rightRead sourceAdd targetAdd
  rw [targetAdd, sumRead, sourceAdd]
  change left x + right x =
    burnolRadiusStateInScaledMeasure left x +
      burnolRadiusStateInScaledMeasure right x
  rw [leftRead, rightRead]

theorem burnolRadiusStateInScaledMeasure_smul
    {radius : ℝ} (coefficient : ℂ)
    (state : BurnolRadiusIntervalL2 radius) :
    burnolRadiusStateInScaledMeasure (coefficient • state) =
      coefficient • burnolRadiusStateInScaledMeasure state := by
  apply Lp.ext
  have sourceRead := Measure.ae_smul_measure
    (Lp.coeFn_smul coefficient state) (ENNReal.ofReal radius⁻¹)
  filter_upwards [
    burnolRadiusStateInScaledMeasure_coe (coefficient • state),
    burnolRadiusStateInScaledMeasure_coe state,
    sourceRead,
    Lp.coeFn_smul coefficient (burnolRadiusStateInScaledMeasure state)]
      with x scaledRead stateRead sourceSmul targetSmul
  rw [targetSmul, scaledRead, sourceSmul]
  change coefficient • state x =
    coefficient • burnolRadiusStateInScaledMeasure state x
  rw [stateRead]

def burnolRadiusStateToScaledMeasure (radius : ℝ) :
    BurnolRadiusIntervalL2 radius →ₗ[ℂ]
      Lp ℂ 2 (burnolRadiusScaledRestrictedMeasure radius) where
  toFun := burnolRadiusStateInScaledMeasure
  map_add' := burnolRadiusStateInScaledMeasure_add
  map_smul' := burnolRadiusStateInScaledMeasure_smul

theorem burnolRadiusScaledState_memLp_restricted
    {radius : ℝ} (positive : 0 < radius)
    (state : Lp ℂ 2 (burnolRadiusScaledRestrictedMeasure radius)) :
    MemLp (state : ℝ → ℂ) 2
      ((volume : Measure ℝ).restrict (symmetricInterval radius)) := by
  have rescaled := (Lp.memLp state).smul_measure
    (c := (ENNReal.ofReal radius⁻¹)⁻¹) (by finiteness)
  have measureEq :
      (ENNReal.ofReal radius⁻¹)⁻¹ •
          burnolRadiusScaledRestrictedMeasure radius =
        (volume : Measure ℝ).restrict (symmetricInterval radius) := by
    unfold burnolRadiusScaledRestrictedMeasure
    rw [smul_smul, ENNReal.inv_mul_cancel
      (burnolRadiusScaledRestrictedMeasure_factor_ne_zero positive)
      (burnolRadiusScaledRestrictedMeasure_factor_ne_top radius), one_smul]
  rw [measureEq] at rescaled
  exact rescaled

def burnolRadiusStateFromScaledMeasure
    {radius : ℝ} (positive : 0 < radius)
    (state : Lp ℂ 2 (burnolRadiusScaledRestrictedMeasure radius)) :
    BurnolRadiusIntervalL2 radius :=
  (burnolRadiusScaledState_memLp_restricted positive state).toLp state

theorem burnolRadiusStateFromScaledMeasure_coe
    {radius : ℝ} (positive : 0 < radius)
    (state : Lp ℂ 2 (burnolRadiusScaledRestrictedMeasure radius)) :
    burnolRadiusStateFromScaledMeasure positive state =ᵐ[
        (volume : Measure ℝ).restrict (symmetricInterval radius)]
      (state : ℝ → ℂ) :=
  MemLp.coeFn_toLp (burnolRadiusScaledState_memLp_restricted positive state)

theorem burnolRadiusStateFromScaledMeasure_add
    {radius : ℝ} (positive : 0 < radius)
    (left right : Lp ℂ 2 (burnolRadiusScaledRestrictedMeasure radius)) :
    burnolRadiusStateFromScaledMeasure positive (left + right) =
      burnolRadiusStateFromScaledMeasure positive left +
        burnolRadiusStateFromScaledMeasure positive right := by
  apply Lp.ext
  have sourceRead : ∀ᵐ x ∂((volume : Measure ℝ).restrict
      (symmetricInterval radius)),
      (left + right : Lp ℂ 2
        (burnolRadiusScaledRestrictedMeasure radius)) x = left x + right x :=
    (Measure.ae_ennreal_smul_measure_iff
      (burnolRadiusScaledRestrictedMeasure_factor_ne_zero positive)).mp
      (Lp.coeFn_add left right)
  filter_upwards [
    burnolRadiusStateFromScaledMeasure_coe positive (left + right),
    burnolRadiusStateFromScaledMeasure_coe positive left,
    burnolRadiusStateFromScaledMeasure_coe positive right,
    sourceRead,
    Lp.coeFn_add (burnolRadiusStateFromScaledMeasure positive left)
      (burnolRadiusStateFromScaledMeasure positive right)]
      with x sumRead leftRead rightRead sourceAdd targetAdd
  rw [targetAdd, sumRead, sourceAdd]
  change left x + right x =
    burnolRadiusStateFromScaledMeasure positive left x +
      burnolRadiusStateFromScaledMeasure positive right x
  rw [leftRead, rightRead]

theorem burnolRadiusStateFromScaledMeasure_smul
    {radius : ℝ} (positive : 0 < radius) (coefficient : ℂ)
    (state : Lp ℂ 2 (burnolRadiusScaledRestrictedMeasure radius)) :
    burnolRadiusStateFromScaledMeasure positive (coefficient • state) =
      coefficient • burnolRadiusStateFromScaledMeasure positive state := by
  apply Lp.ext
  have sourceRead : ∀ᵐ x ∂((volume : Measure ℝ).restrict
      (symmetricInterval radius)),
      (coefficient • state : Lp ℂ 2
        (burnolRadiusScaledRestrictedMeasure radius)) x =
          coefficient • state x :=
    (Measure.ae_ennreal_smul_measure_iff
      (burnolRadiusScaledRestrictedMeasure_factor_ne_zero positive)).mp
      (Lp.coeFn_smul coefficient state)
  filter_upwards [
    burnolRadiusStateFromScaledMeasure_coe positive (coefficient • state),
    burnolRadiusStateFromScaledMeasure_coe positive state,
    sourceRead,
    Lp.coeFn_smul coefficient
      (burnolRadiusStateFromScaledMeasure positive state)]
      with x scaledRead stateRead sourceSmul targetSmul
  rw [targetSmul, scaledRead, sourceSmul]
  change coefficient • state x =
    coefficient • burnolRadiusStateFromScaledMeasure positive state x
  rw [stateRead]

def burnolRadiusStateFromScaledMeasureLinear
    {radius : ℝ} (positive : 0 < radius) :
    Lp ℂ 2 (burnolRadiusScaledRestrictedMeasure radius) →ₗ[ℂ]
      BurnolRadiusIntervalL2 radius where
  toFun := burnolRadiusStateFromScaledMeasure positive
  map_add' := burnolRadiusStateFromScaledMeasure_add positive
  map_smul' := burnolRadiusStateFromScaledMeasure_smul positive

def burnolRadiusScaleComposition
    {radius : ℝ} (positive : 0 < radius) :
    Lp ℂ 2 (burnolRadiusScaledRestrictedMeasure radius) →ₗᵢ[ℂ]
      BurnolUnitIntervalL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (burnolRadiusScale radius)
    (burnolRadiusScaleMeasurePreserving positive)

def burnolRadiusRechartValue
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolRadiusIntervalL2 radius) : BurnolUnitIntervalL2 :=
  (Real.sqrt radius : ℂ) •
    burnolRadiusScaleComposition positive
      (burnolRadiusStateInScaledMeasure state)

theorem burnolRadiusRechartValue_add
    {radius : ℝ} (positive : 0 < radius)
    (left right : BurnolRadiusIntervalL2 radius) :
    burnolRadiusRechartValue positive (left + right) =
      burnolRadiusRechartValue positive left +
        burnolRadiusRechartValue positive right := by
  simp only [burnolRadiusRechartValue, burnolRadiusStateInScaledMeasure_add,
    map_add, smul_add]

theorem burnolRadiusRechartValue_smul
    {radius : ℝ} (positive : 0 < radius) (coefficient : ℂ)
    (state : BurnolRadiusIntervalL2 radius) :
    burnolRadiusRechartValue positive (coefficient • state) =
      coefficient • burnolRadiusRechartValue positive state := by
  simp only [burnolRadiusRechartValue, burnolRadiusStateInScaledMeasure_smul,
    map_smul, smul_smul]
  rw [mul_comm (Real.sqrt radius : ℂ) coefficient]

theorem burnolRadiusRechartValue_norm
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolRadiusIntervalL2 radius) :
    ‖burnolRadiusRechartValue positive state‖ = ‖state‖ := by
  rw [burnolRadiusRechartValue, norm_smul,
    (burnolRadiusScaleComposition positive).norm_map,
    burnolRadiusStateInScaledMeasure_norm positive]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg radius)]
  have cancelRoot :
      Real.sqrt radius * Real.sqrt radius⁻¹ = 1 := by
    rw [← Real.sqrt_mul positive.le, mul_inv_cancel₀ positive.ne', Real.sqrt_one]
  rw [← mul_assoc, cancelRoot, one_mul]

def burnolRadiusRechart
    {radius : ℝ} (positive : 0 < radius) :
    BurnolRadiusIntervalL2 radius →ₗᵢ[ℂ] BurnolUnitIntervalL2 where
  toLinearMap :=
    { toFun := burnolRadiusRechartValue positive
      map_add' := burnolRadiusRechartValue_add positive
      map_smul' := burnolRadiusRechartValue_smul positive }
  norm_map' := burnolRadiusRechartValue_norm positive

theorem burnolRadiusRechart_coe
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolRadiusIntervalL2 radius) :
    (burnolRadiusRechart positive state : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ).restrict (symmetricInterval 1)]
      fun x ↦ (Real.sqrt radius : ℂ) • state (radius * x) := by
  have compositionRead := Lp.coeFn_compMeasurePreserving
    (burnolRadiusStateInScaledMeasure state)
    (burnolRadiusScaleMeasurePreserving positive)
  have sourceRead :=
    (burnolRadiusScaleMeasurePreserving positive).quasiMeasurePreserving.ae_eq
      (burnolRadiusStateInScaledMeasure_coe state)
  filter_upwards [
    Lp.coeFn_smul (Real.sqrt radius : ℂ)
      (burnolRadiusScaleComposition positive
        (burnolRadiusStateInScaledMeasure state)),
    compositionRead, sourceRead]
      with x scaledRead compositionAt sourceAt
  change ((Real.sqrt radius : ℂ) •
    burnolRadiusScaleComposition positive
      (burnolRadiusStateInScaledMeasure state) : BurnolUnitIntervalL2) x = _
  have compositionAt' :
      (burnolRadiusScaleComposition positive
          (burnolRadiusStateInScaledMeasure state) : ℝ → ℂ) x =
        (burnolRadiusStateInScaledMeasure state : ℝ → ℂ)
          (radius * x) := by
    change (Lp.compMeasurePreserving (burnolRadiusScale radius)
      (burnolRadiusScaleMeasurePreserving positive)
      (burnolRadiusStateInScaledMeasure state) : ℝ → ℂ) x = _
    simpa only [burnolRadiusScale, Function.comp_apply] using compositionAt
  have sourceAt' :
      (burnolRadiusStateInScaledMeasure state : ℝ → ℂ) (radius * x) =
        state (radius * x) := by
    simpa only [burnolRadiusScale, Function.comp_apply] using sourceAt
  rw [scaledRead]
  change (Real.sqrt radius : ℂ) •
    (burnolRadiusScaleComposition positive
      (burnolRadiusStateInScaledMeasure state) : ℝ → ℂ) x = _
  rw [compositionAt', sourceAt']

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
