import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadWeightedSum
open Set Filter MeasureTheory
noncomputable section
variable {Index : Type*} {μ : Measure ℝ}
  (f : Index → ℝ → ℂ) (integrable : ∀ index, Integrable (f index) μ)
  (summable : Summable (fun index => ∫ time, ‖f index time‖ ∂μ))
  (kernel : ℝ → ℝ) (measurable : AEStronglyMeasurable kernel μ)
  (cap : ℝ) (bounded : ∀ᵐ time ∂μ, ‖kernel time‖ ≤ cap)

include integrable measurable bounded

theorem weighted_integrable (index : Index) : Integrable (fun time => kernel time • f index time) μ := by
  apply ((integrable index).norm.const_mul cap).mono' (measurable.smul (integrable index).aestronglyMeasurable)
  filter_upwards [bounded] with time generated
  change ‖kernel time • f index time‖ ≤ cap * ‖f index time‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right generated (norm_nonneg _)

theorem weighted_integral_bound (index : Index) :
    (∫ time, ‖kernel time • f index time‖ ∂μ) ≤ cap * ∫ time, ‖f index time‖ ∂μ := by
  rw [← integral_const_mul]
  apply integral_mono_ae (weighted_integrable f integrable kernel measurable cap bounded index).norm
    ((integrable index).norm.const_mul cap)
  filter_upwards [bounded] with time generated
  change ‖kernel time • f index time‖ ≤ cap * ‖f index time‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right generated (norm_nonneg _)

include summable

theorem weighted_summable : Summable (fun index => ∫ time, ‖kernel time • f index time‖ ∂μ) :=
  (summable.mul_left cap).of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (weighted_integral_bound f integrable kernel measurable cap bounded)

theorem integrals_summable : Summable (fun index => ∫ time, kernel time • f index time ∂μ) := by
  apply Summable.of_norm
  exact (weighted_summable f integrable summable kernel measurable cap bounded).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun index => norm_integral_le_integral_norm _)

variable [Countable Index]

theorem weighted_integral_tsum (pointwise : ∀ᵐ time ∂μ, Summable (fun index => f index time)) :
    (∫ time, kernel time • ∑' index, f index time ∂μ) =
      ∑' index, ∫ time, kernel time • f index time ∂μ := by
  rw [integral_tsum_of_summable_integral_norm
    (weighted_integrable f integrable kernel measurable cap bounded)
    (weighted_summable f integrable summable kernel measurable cap bounded)]
  apply integral_congr_ae
  filter_upwards [pointwise] with time generated
  exact (generated.tsum_const_smul (kernel time)).symm

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadWeightedSum
