import H0mework.Arithmetic.TruncatedFourier.MeasureRechart

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Pointwise

noncomputable section

def burnolRadiusScaleMeasurableEquiv
    {radius : ℝ} (positive : 0 < radius) : ℝ ≃ᵐ ℝ :=
  (Homeomorph.mulLeft₀ radius positive.ne').toMeasurableEquiv

@[simp]
theorem burnolRadiusScaleMeasurableEquiv_apply
    {radius : ℝ} (positive : 0 < radius) (x : ℝ) :
    burnolRadiusScaleMeasurableEquiv positive x = radius * x :=
  rfl

@[simp]
theorem burnolRadiusScaleMeasurableEquiv_symm_apply
    {radius : ℝ} (positive : 0 < radius) (x : ℝ) :
    (burnolRadiusScaleMeasurableEquiv positive).symm x = radius⁻¹ * x :=
  rfl

theorem burnolRadiusScaleEquiv_measurePreserving
    {radius : ℝ} (positive : 0 < radius) :
    MeasurePreserving (burnolRadiusScaleMeasurableEquiv positive)
      ((volume : Measure ℝ).restrict (symmetricInterval 1))
      (burnolRadiusScaledRestrictedMeasure radius) where
  measurable := (burnolRadiusScaleMeasurableEquiv positive).measurable
  map_eq := by
    change Measure.map (burnolRadiusScale radius)
      ((volume : Measure ℝ).restrict (symmetricInterval 1)) = _
    exact burnolRadiusScale_map_restricted positive

theorem burnolRadiusScaleEquiv_symm_measurePreserving
    {radius : ℝ} (positive : 0 < radius) :
    MeasurePreserving (burnolRadiusScaleMeasurableEquiv positive).symm
      (burnolRadiusScaledRestrictedMeasure radius)
      ((volume : Measure ℝ).restrict (symmetricInterval 1)) :=
  (burnolRadiusScaleEquiv_measurePreserving positive).symm

def burnolRadiusInverseScaleComposition
    {radius : ℝ} (positive : 0 < radius) :
    BurnolUnitIntervalL2 →ₗᵢ[ℂ]
      Lp ℂ 2 (burnolRadiusScaledRestrictedMeasure radius) :=
  Lp.compMeasurePreservingₗᵢ ℂ
    (burnolRadiusScaleMeasurableEquiv positive).symm
    (burnolRadiusScaleEquiv_symm_measurePreserving positive)

def burnolRadiusInverseRechartValue
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolUnitIntervalL2) : BurnolRadiusIntervalL2 radius :=
  (Real.sqrt radius : ℂ)⁻¹ •
    burnolRadiusStateFromScaledMeasure positive
      (burnolRadiusInverseScaleComposition positive state)

theorem burnolRadiusInverseRechartValue_add
    {radius : ℝ} (positive : 0 < radius)
    (left right : BurnolUnitIntervalL2) :
    burnolRadiusInverseRechartValue positive (left + right) =
      burnolRadiusInverseRechartValue positive left +
        burnolRadiusInverseRechartValue positive right := by
  simp only [burnolRadiusInverseRechartValue, map_add,
    burnolRadiusStateFromScaledMeasure_add, smul_add]

theorem burnolRadiusInverseRechartValue_smul
    {radius : ℝ} (positive : 0 < radius) (coefficient : ℂ)
    (state : BurnolUnitIntervalL2) :
    burnolRadiusInverseRechartValue positive (coefficient • state) =
      coefficient • burnolRadiusInverseRechartValue positive state := by
  simp only [burnolRadiusInverseRechartValue, map_smul,
    burnolRadiusStateFromScaledMeasure_smul, smul_smul]
  rw [mul_comm (Real.sqrt radius : ℂ)⁻¹ coefficient]

def burnolRadiusInverseRechart
    {radius : ℝ} (positive : 0 < radius) :
    BurnolUnitIntervalL2 →ₗ[ℂ] BurnolRadiusIntervalL2 radius where
  toFun := burnolRadiusInverseRechartValue positive
  map_add' := burnolRadiusInverseRechartValue_add positive
  map_smul' := burnolRadiusInverseRechartValue_smul positive

theorem burnolRadiusInverseRechart_coe
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolUnitIntervalL2) :
    (burnolRadiusInverseRechart positive state : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ).restrict (symmetricInterval radius)]
      fun x ↦ (Real.sqrt radius : ℂ)⁻¹ • state (radius⁻¹ * x) := by
  have compositionRead := Lp.coeFn_compMeasurePreserving state
    (burnolRadiusScaleEquiv_symm_measurePreserving positive)
  have compositionReadRestricted :
      (burnolRadiusInverseScaleComposition positive state : ℝ → ℂ) =ᵐ[
          (volume : Measure ℝ).restrict (symmetricInterval radius)]
        (state : ℝ → ℂ) ∘
          (burnolRadiusScaleMeasurableEquiv positive).symm := by
    apply (Measure.ae_ennreal_smul_measure_iff
      (burnolRadiusScaledRestrictedMeasure_factor_ne_zero positive)).mp
    change (Lp.compMeasurePreserving
      (burnolRadiusScaleMeasurableEquiv positive).symm
      (burnolRadiusScaleEquiv_symm_measurePreserving positive) state :
        ℝ → ℂ) =ᵐ[burnolRadiusScaledRestrictedMeasure radius]
      (state : ℝ → ℂ) ∘
        (burnolRadiusScaleMeasurableEquiv positive).symm
    exact compositionRead
  have scaledRead := burnolRadiusStateFromScaledMeasure_coe positive
    (burnolRadiusInverseScaleComposition positive state)
  filter_upwards [
    Lp.coeFn_smul (Real.sqrt radius : ℂ)⁻¹
      (burnolRadiusStateFromScaledMeasure positive
        (burnolRadiusInverseScaleComposition positive state)),
    scaledRead, compositionReadRestricted]
      with x scalarAt scaledAt compositionAt
  change ((Real.sqrt radius : ℂ)⁻¹ •
    burnolRadiusStateFromScaledMeasure positive
      (burnolRadiusInverseScaleComposition positive state) :
        BurnolRadiusIntervalL2 radius) x = _
  rw [scalarAt]
  change (Real.sqrt radius : ℂ)⁻¹ •
    burnolRadiusStateFromScaledMeasure positive
      (burnolRadiusInverseScaleComposition positive state) x = _
  rw [scaledAt]
  have compositionAt' :
      (burnolRadiusInverseScaleComposition positive state : ℝ → ℂ) x =
        state (radius⁻¹ * x) := by
    simpa only [burnolRadiusScaleMeasurableEquiv_symm_apply,
      Function.comp_apply] using compositionAt
  rw [compositionAt']

theorem burnolRadiusRechart_inverse_apply
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolUnitIntervalL2) :
    burnolRadiusRechart positive
        (burnolRadiusInverseRechart positive state) = state := by
  apply Lp.ext
  have inverseScaled := Measure.ae_smul_measure
    (burnolRadiusInverseRechart_coe positive state)
    (ENNReal.ofReal radius⁻¹)
  have inverseRead :=
    (burnolRadiusScaleEquiv_measurePreserving positive).quasiMeasurePreserving.ae_eq
      inverseScaled
  filter_upwards [
    burnolRadiusRechart_coe positive
      (burnolRadiusInverseRechart positive state),
    inverseRead]
      with x forwardAt inverseAt
  rw [forwardAt]
  have inverseAt' :
      (burnolRadiusInverseRechart positive state : ℝ → ℂ)
          (radius * x) =
        (Real.sqrt radius : ℂ)⁻¹ • state (radius⁻¹ * (radius * x)) := by
    simpa only [burnolRadiusScaleMeasurableEquiv_apply,
      Function.comp_apply] using inverseAt
  rw [inverseAt']
  simp only [smul_smul]
  rw [mul_inv_cancel₀]
  · simp [positive.ne']
  · exact_mod_cast (Real.sqrt_pos.2 positive).ne'

theorem burnolRadiusRechart_surjective
    {radius : ℝ} (positive : 0 < radius) :
    Function.Surjective (burnolRadiusRechart positive) := by
  intro state
  exact ⟨burnolRadiusInverseRechart positive state,
    burnolRadiusRechart_inverse_apply positive state⟩

def burnolRadiusRechartEquiv
    {radius : ℝ} (positive : 0 < radius) :
    BurnolRadiusIntervalL2 radius ≃ₗᵢ[ℂ] BurnolUnitIntervalL2 :=
  LinearIsometryEquiv.ofSurjective (burnolRadiusRechart positive)
    (burnolRadiusRechart_surjective positive)

@[simp]
theorem burnolRadiusRechartEquiv_apply
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolRadiusIntervalL2 radius) :
    burnolRadiusRechartEquiv positive state = burnolRadiusRechart positive state :=
  rfl

@[simp]
theorem burnolRadiusRechartEquiv_symm_apply
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolUnitIntervalL2) :
    (burnolRadiusRechartEquiv positive).symm state =
      burnolRadiusInverseRechart positive state := by
  apply (burnolRadiusRechart positive).injective
  rw [← burnolRadiusRechartEquiv_apply]
  rw [(burnolRadiusRechartEquiv positive).apply_symm_apply]
  exact (burnolRadiusRechart_inverse_apply positive state).symm

theorem burnolRadiusRechartEquiv_symm_coe
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolUnitIntervalL2) :
    ((burnolRadiusRechartEquiv positive).symm state : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ).restrict (symmetricInterval radius)]
      fun x ↦ (Real.sqrt radius : ℂ)⁻¹ • state (radius⁻¹ * x) := by
  rw [burnolRadiusRechartEquiv_symm_apply]
  exact burnolRadiusInverseRechart_coe positive state

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
