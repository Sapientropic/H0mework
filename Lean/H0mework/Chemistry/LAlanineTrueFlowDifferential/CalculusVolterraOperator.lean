import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusPath

/-!
The bounded Volterra operator on the actual symmetric time window. Its primitive uses
the clamped continuous extension and retains the orientation of negative-time integrals.
-/

set_option autoImplicit false

namespace LAlanineTrueFlowDifferential

noncomputable section

/-- Continuous clamped extension of a path beyond its actual time window. -/
def extendPath (η : Path) (t : ℝ) : Space :=
  η (Set.projIcc (-(1 / 2) : ℝ) (1 / 2) (by norm_num) t)

theorem continuous_extendPath (η : Path) : Continuous (extendPath η) :=
  η.continuous.comp continuous_projIcc

@[simp] theorem extendPath_coe (η : Path) (t : Time) : extendPath η t = η t := by
  simp [extendPath]

/-- The actual oriented primitive, extended as a differentiable map on real time. -/
def pathPrimitive (η : Path) (t : ℝ) : Space := ∫ s in 0..t, extendPath η s

theorem continuous_pathPrimitive (η : Path) : Continuous (pathPrimitive η) :=
  intervalIntegral.continuous_primitive
    (fun a b => (continuous_extendPath η).intervalIntegrable a b) 0

private def volterraLinearMap : Path →ₗ[ℝ] Path where
  toFun η := ⟨fun t => pathPrimitive η t,
    (continuous_pathPrimitive η).comp continuous_subtype_val⟩
  map_add' η ξ := by
    apply ContinuousMap.ext
    intro t
    change (∫ s in 0..(t : ℝ), extendPath η s + extendPath ξ s) = _
    exact intervalIntegral.integral_add
      ((continuous_extendPath η).intervalIntegrable 0 t)
      ((continuous_extendPath ξ).intervalIntegrable 0 t)
  map_smul' c η := by
    apply ContinuousMap.ext
    intro t
    change (∫ s in 0..(t : ℝ), c • extendPath η s) = _
    exact intervalIntegral.integral_smul c (extendPath η)

private theorem volterra_bound (η : Path) :
    ‖volterraLinearMap η‖ ≤ (1 / 2 : ℝ) * ‖η‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  calc
    ‖volterraLinearMap η t‖ ≤ ‖η‖ * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun s _ =>
        η.norm_coe_le_norm _
    _ ≤ ‖η‖ * (1 / 2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg η)
      simpa only [sub_zero] using abs_le.mpr t.property
    _ = (1 / 2 : ℝ) * ‖η‖ := mul_comm _ _

/-- Oriented integration from zero as a bounded linear operator on the path sup norm. -/
def volterra : Path →L[ℝ] Path :=
  volterraLinearMap.mkContinuous (1 / 2) volterra_bound

@[simp] theorem volterra_apply (η : Path) (t : Time) :
    volterra η t = ∫ s in 0..(t : ℝ), extendPath η s := rfl

theorem norm_volterra_le : ‖volterra‖ ≤ (1 / 2 : ℝ) :=
  volterraLinearMap.mkContinuous_norm_le (by norm_num) volterra_bound

@[simp] theorem volterra_apply_zero (η : Path) : volterra η zeroTime = 0 := by
  simp [zeroTime]

set_option backward.isDefEq.respectTransparency false in
/-- FTC for the same primitive at every actual time, including both endpoints. -/
theorem hasDerivAt_pathPrimitive (η : Path) (t : Time) :
    HasDerivAt (pathPrimitive η) (η t) (t : ℝ) := by
  change HasDerivAt (fun u => ∫ s in 0..u, extendPath η s) (η t) (t : ℝ)
  rw [← extendPath_coe η t]
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_extendPath η).intervalIntegrable 0 t)
    (continuous_extendPath η).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_extendPath η).continuousAt

/-- Initial-value injection, using the existing constant-path continuous linear map. -/
abbrev pathConst : Space →L[ℝ] Path := ContinuousLinearMap.const ℝ Time

theorem norm_volterra_comp_le (M : Path →L[ℝ] Path) {K : ℝ} (hM : ‖M‖ ≤ K) :
    ‖volterra.comp M‖ ≤ K / 2 := by
  calc
    ‖volterra.comp M‖ ≤ ‖volterra‖ * ‖M‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (1 / 2 : ℝ) * ‖M‖ := mul_le_mul_of_nonneg_right norm_volterra_le (norm_nonneg M)
    _ ≤ (1 / 2 : ℝ) * K := mul_le_mul_of_nonneg_left hM (by norm_num)
    _ = K / 2 := by ring

end

end LAlanineTrueFlowDifferential
