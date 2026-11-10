import Mathlib.MeasureTheory.Function.Holder

/-! A bounded measurable Banach-valued kernel integrates all L1 scalar inputs. -/

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace SaturationMonoid.Quantum.Dynamics.Smearing
noncomputable section

variable {X B : Type*} [MeasurableSpace X] [NormedAddCommGroup B] [NormedSpace ℂ B]
    [CompleteSpace B] (μ : Measure X) (K : X → B)
    (measurable : AEStronglyMeasurable K μ) (C : ℝ) (bounded : ∀ p, ‖K p‖ ≤ C)

include measurable bounded in
omit [CompleteSpace B] [NormedSpace ℂ B] in
private theorem kernel_memLp : MemLp K ⊤ μ :=
  memLp_top_of_bound measurable C (Filter.Eventually.of_forall bounded)

private def kernelLp : Lp B ⊤ μ := (kernel_memLp μ K measurable C bounded).toLp K

def integralMap : Lp ℂ 1 μ →L[ℂ] B :=
  ((ContinuousLinearMap.lsmul ℂ ℂ).lpPairing μ 1 ⊤).flip (kernelLp μ K measurable C bounded)

theorem integralMap_apply (f : Lp ℂ 1 μ) :
    integralMap μ K measurable C bounded f = ∫ p, f p • K p ∂μ := by
  change (ContinuousLinearMap.lsmul ℂ ℂ).lpPairing μ 1 ⊤ f
    (kernelLp μ K measurable C bounded) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(kernel_memLp μ K measurable C bounded).coeFn_toLp] with p same
  exact congrArg (f p • ·) same

include measurable bounded in
omit [CompleteSpace B] in
theorem kernel_integrable (f : Lp ℂ 1 μ) : Integrable (fun p => f p • K p) μ :=
  (L1.integrable_coeFn f).smul_bdd C measurable (Filter.Eventually.of_forall bounded)

end
end SaturationMonoid.Quantum.Dynamics.Smearing
