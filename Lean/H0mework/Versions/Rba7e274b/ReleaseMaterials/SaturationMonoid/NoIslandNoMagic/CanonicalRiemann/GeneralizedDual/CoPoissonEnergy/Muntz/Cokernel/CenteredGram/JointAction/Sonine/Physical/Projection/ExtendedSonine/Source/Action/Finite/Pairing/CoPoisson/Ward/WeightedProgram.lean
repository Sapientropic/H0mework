import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.Weighted
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.WeightedProgram

open Complex Filter MeasureTheory Set
open scoped Topology
noncomputable section

private def step (primitive : BurnolL2) (lower upper : ℝ) : BurnolL2 :=
  burnolSourceScalePrimitive primitive upper - burnolSourceScalePrimitive primitive lower

/-- The original weighted algorithm acts on one common source primitive. -/
def program (lower upper : ℝ) (f f' : ℝ → ℂ) (primitive : BurnolL2) : BurnolL2 :=
  f upper • step primitive lower upper -
    ∫ u : ℝ in Ioc lower upper, f' u • step primitive lower u

theorem program_original (lower upper : ℝ) (f f' : ℝ → ℂ) :
    program lower upper f f' burnolUnitCountingPrimitiveL2 =
      burnolWeightedReciprocalStepWave lower upper f f' := rfl

private theorem scale_norm (primitive : BurnolL2) (radius : ℝ) :
    ‖burnolSourceScalePrimitive primitive radius‖ = Real.sqrt radius * ‖primitive‖ := by
  simp only [burnolSourceScalePrimitive, norm_smul,
    (burnolMultiplicativeDilation (Real.log radius)).norm_map, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg radius)]

private theorem step_norm_le (primitive : BurnolL2) (lower upper u : ℝ)
    (inside : u ∈ Icc lower upper) :
    ‖step primitive lower u‖ ≤ (2 * Real.sqrt upper) * ‖primitive‖ := by
  have first := Real.sqrt_le_sqrt inside.2
  have second := Real.sqrt_le_sqrt (inside.1.trans inside.2)
  calc
    _ ≤ ‖burnolSourceScalePrimitive primitive u‖ +
        ‖burnolSourceScalePrimitive primitive lower‖ := norm_sub_le _ _
    _ = (Real.sqrt u + Real.sqrt lower) * ‖primitive‖ := by rw [scale_norm, scale_norm]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

private theorem step_continuous (lower radius : ℝ) :
    Continuous (fun primitive : BurnolL2 => step primitive lower radius) := by
  unfold step burnolSourceScalePrimitive
  exact ((burnolMultiplicativeDilation (Real.log radius)).continuous.const_smul
    (Real.sqrt radius)).sub
    ((burnolMultiplicativeDilation (Real.log lower)).continuous.const_smul (Real.sqrt lower))

private theorem family_integrable (lower upper : ℝ) (f' : ℝ → ℂ)
    (positive : 0 < lower) (regular : ContinuousOn f' (Icc lower upper))
    (primitive : BurnolL2) :
    IntegrableOn (fun u => f' u • step primitive lower u) (Ioc lower upper) := by
  have varying : ContinuousOn (fun u => step primitive lower u) (Icc lower upper) :=
    ((burnolSourceScalePrimitive_continuous primitive).mono
      (fun _ inside => positive.trans_le inside.1)).sub continuousOn_const
  exact (regular.smul varying).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- Source primitive convergence passes through the complete weighted Bochner
algorithm; its original normalization is part of the same operation. -/
theorem program_tendsto (lower upper : ℝ) (f f' : ℝ → ℂ)
    (positive : 0 < lower)
    (regular : ContinuousOn f' (Icc lower upper))
    (primitives : ℕ → BurnolL2) (primitive : BurnolL2)
    (convergence : Tendsto primitives atTop (𝓝 primitive)) :
    Tendsto (fun N => program lower upper f f' (primitives N)) atTop
      (𝓝 (program lower upper f f' primitive)) := by
  let M := ‖primitive‖ + 1
  have bounded : ∀ᶠ N : ℕ in atTop, ‖primitives N‖ < M :=
    (tendsto_order.1 convergence.norm).2 M (by dsimp [M]; linarith)
  let bound : ℝ → ℝ := fun u => ‖f' u‖ * ((2 * Real.sqrt upper) * M)
  have measured : ∀ᶠ N : ℕ in atTop,
      AEStronglyMeasurable (fun u => f' u • step (primitives N) lower u)
        (volume.restrict (Ioc lower upper)) :=
    Filter.Eventually.of_forall (fun N =>
      (family_integrable lower upper f' positive regular (primitives N)).aestronglyMeasurable)
  have dominated : ∀ᶠ N : ℕ in atTop, ∀ᵐ u ∂volume.restrict (Ioc lower upper),
      ‖f' u • step (primitives N) lower u‖ ≤ bound u := by
    filter_upwards [bounded] with N boundN
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (step_norm_le (primitives N) lower upper u ⟨inside.1.le, inside.2⟩).trans
      (mul_le_mul_of_nonneg_left boundN.le (by positivity))
  have boundIntegral : Integrable bound (volume.restrict (Ioc lower upper)) :=
    (regular.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mul_const _
  have pointwise : ∀ᵐ u ∂volume.restrict (Ioc lower upper),
      Tendsto (fun N => f' u • step (primitives N) lower u) atTop
        (𝓝 (f' u • step primitive lower u)) := by
    filter_upwards with u
    exact (((step_continuous lower u).tendsto primitive).comp convergence).const_smul (f' u)
  have integralLimit := tendsto_integral_filter_of_dominated_convergence
    bound measured dominated boundIntegral pointwise
  have headLimit := (((step_continuous lower upper).tendsto primitive).comp convergence).const_smul
    (f upper)
  exact headLimit.sub integralLimit

end
end OriginalRieszFinitePairing.CoPoisson.Ward.WeightedProgram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
