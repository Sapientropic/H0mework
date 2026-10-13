import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WeightedProgram
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.InfiniteWeightedProgram

open Complex Filter MeasureTheory Set
open scoped Topology
noncomputable section

private def step (primitive : BurnolL2) (upper : ℝ) : BurnolL2 :=
  burnolSourceScalePrimitive primitive upper - burnolSourceScalePrimitive primitive 4

def weight (derivative : ℝ → ℂ) (upper : ℝ) : ℝ := ‖derivative upper‖ * (Real.sqrt upper + 2)

def program (derivative : ℝ → ℂ) (primitive : BurnolL2) : BurnolL2 :=
  -(∫ upper : ℝ in Ioi 4, derivative upper • step primitive upper)

private theorem sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

private theorem step_norm (primitive : BurnolL2) (upper : ℝ) :
    ‖step primitive upper‖ ≤ (Real.sqrt upper + 2) * ‖primitive‖ := by
  unfold step
  have source (radius : ℝ) : ‖burnolSourceScalePrimitive primitive radius‖ =
      Real.sqrt radius * ‖primitive‖ := by
    simp only [burnolSourceScalePrimitive, norm_smul, LinearIsometryEquiv.norm_map,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg radius)]
  calc
    _ ≤ ‖burnolSourceScalePrimitive primitive upper‖ +
      ‖burnolSourceScalePrimitive primitive 4‖ := norm_sub_le _ _
    _ = _ := by rw [source, source, sqrt_four]; ring

private theorem step_continuous (upper : ℝ) : Continuous (fun primitive : BurnolL2 => step primitive upper) := by
  unfold step burnolSourceScalePrimitive
  exact ((burnolMultiplicativeDilation (Real.log upper)).continuous.const_smul (Real.sqrt upper)).sub
    ((burnolMultiplicativeDilation (Real.log 4)).continuous.const_smul (Real.sqrt 4))

private theorem family_measurable (derivative : ℝ → ℂ) (measured : Measurable derivative)
    (primitive : BurnolL2) :
    AEStronglyMeasurable (fun upper : ℝ => derivative upper • step primitive upper)
      (volume.restrict (Ioi 4)) := by
  have regular : ContinuousOn (step primitive) (Ioi 4) :=
    ((burnolSourceScalePrimitive_continuous primitive).mono
      (fun _ inside => (by norm_num : (0 : ℝ) < 4).trans inside)).sub continuousOn_const
  exact measured.aestronglyMeasurable.smul (regular.aestronglyMeasurable measurableSet_Ioi)

/-- The complete original weighted programme is integrable on the unbounded source interval. -/
theorem family_integrable (derivative : ℝ → ℂ) (measured : Measurable derivative)
    (summable : IntegrableOn (weight derivative) (Ioi 4)) (primitive : BurnolL2) :
    IntegrableOn (fun upper : ℝ => derivative upper • step primitive upper) (Ioi 4) := by
  apply (summable.mul_const ‖primitive‖).mono' (family_measurable derivative measured primitive)
  filter_upwards with upper
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (step_norm primitive upper) (norm_nonneg _)).trans_eq
    (by unfold weight; ring)

/-- The original strong primitive limit passes through the whole source tail at once. -/
theorem program_tendsto (derivative : ℝ → ℂ) (measured : Measurable derivative)
    (summable : IntegrableOn (weight derivative) (Ioi 4))
    (primitives : ℕ → BurnolL2) (primitive : BurnolL2)
    (convergence : Tendsto primitives atTop (𝓝 primitive)) :
    Tendsto (fun N => program derivative (primitives N)) atTop (𝓝 (program derivative primitive)) := by
  let M := ‖primitive‖ + 1
  have bounded : ∀ᶠ N : ℕ in atTop, ‖primitives N‖ < M :=
    (tendsto_order.1 convergence.norm).2 M (by dsimp [M]; linarith)
  have measuredFamily : ∀ᶠ N : ℕ in atTop,
      AEStronglyMeasurable (fun upper : ℝ => derivative upper • step (primitives N) upper)
        (volume.restrict (Ioi 4)) :=
    Eventually.of_forall (fun N => family_measurable derivative measured (primitives N))
  have dominated : ∀ᶠ N : ℕ in atTop, ∀ᵐ upper ∂volume.restrict (Ioi 4),
      ‖derivative upper • step (primitives N) upper‖ ≤ weight derivative upper * M := by
    filter_upwards [bounded] with N boundN
    filter_upwards with upper
    rw [norm_smul]
    calc
      _ ≤ ‖derivative upper‖ * ((Real.sqrt upper + 2) * ‖primitives N‖) :=
        mul_le_mul_of_nonneg_left (step_norm (primitives N) upper) (norm_nonneg _)
      _ = weight derivative upper * ‖primitives N‖ := by unfold weight; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left boundN.le (by unfold weight; positivity)
  have pointwise : ∀ᵐ upper ∂volume.restrict (Ioi 4),
      Tendsto (fun N => derivative upper • step (primitives N) upper) atTop
        (𝓝 (derivative upper • step primitive upper)) := by
    filter_upwards with upper
    exact (((step_continuous upper).tendsto primitive).comp convergence).const_smul _
  exact (tendsto_integral_filter_of_dominated_convergence _ measuredFamily dominated
    (summable.mul_const M) pointwise).neg

/-- The finite weighted head disappears by its actual decay; the full source integral remains. -/
theorem finite_program_tendsto (f derivative : ℝ → ℂ) (measured : Measurable derivative)
    (summable : IntegrableOn (weight derivative) (Ioi 4))
    (head : Tendsto (fun upper : ℝ => Real.sqrt upper * ‖f upper‖) atTop (𝓝 0))
    (primitive : BurnolL2) :
    Tendsto (fun upper : ℝ => WeightedProgram.program 4 upper f derivative primitive) atTop
      (𝓝 (program derivative primitive)) := by
  have headLimit : Tendsto (fun upper : ℝ => f upper • step primitive upper) atTop (𝓝 0) := by
    have bound : ∀ᶠ upper : ℝ in atTop, ‖f upper • step primitive upper‖ ≤
        (2 * (Real.sqrt upper * ‖f upper‖)) * ‖primitive‖ := by
      filter_upwards [eventually_ge_atTop (4 : ℝ)] with upper after
      have root : (2 : ℝ) ≤ Real.sqrt upper := by
        simpa only [sqrt_four] using Real.sqrt_le_sqrt after
      rw [norm_smul]
      calc
        _ ≤ ‖f upper‖ * ((Real.sqrt upper + 2) * ‖primitive‖) :=
          mul_le_mul_of_nonneg_left (step_norm primitive upper) (norm_nonneg _)
        _ = (Real.sqrt upper + 2) * (‖f upper‖ * ‖primitive‖) := by ring
        _ ≤ (2 * Real.sqrt upper) * (‖f upper‖ * ‖primitive‖) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = (2 * (Real.sqrt upper * ‖f upper‖)) * ‖primitive‖ := by ring
    apply squeeze_zero_norm' bound
    simpa only [mul_zero, zero_mul] using (head.const_mul 2).mul_const ‖primitive‖
  have integralLimit := intervalIntegral_tendsto_integral_Ioi 4
    (family_integrable derivative measured summable primitive) (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)
  have setLimit : Tendsto (fun upper : ℝ =>
      ∫ u : ℝ in Ioc 4 upper, derivative u • step primitive u) atTop
        (𝓝 (∫ u : ℝ in Ioi 4, derivative u • step primitive u)) := by
    apply integralLimit.congr'
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with upper after
    exact intervalIntegral.integral_of_le after
  have actual := headLimit.sub setLimit
  simp only [zero_sub] at actual
  exact actual

end
end OriginalRieszFinitePairing.CoPoisson.Ward.InfiniteWeightedProgram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
