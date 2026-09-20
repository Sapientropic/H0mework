import H0mework.Quantum.Generator.Core
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Dense generator domain from time averages

Integrating a continuous isometric orbit in a complex Banach space over a finite time interval produces
a differentiable vector. Dividing by the interval length recovers the source
vector in the zero-length limit, so the actual generator domain is dense.
-/

set_option autoImplicit false

open scoped Topology
open Filter MeasureTheory

namespace SaturationMonoid.Quantum.Generator

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (U : Multiplicative ℝ →* (E ≃ₗᵢ[ℂ] E))
  (continuousOrbit : ∀ x, Continuous (orbit U x))

/-- A finite orbit integral generated from one source vector. -/
def timeIntegral (x : E) (a : ℝ) : E := ∫ s in 0..a, orbit U x s

theorem orbit_timeIntegral (x : E) (a t : ℝ) :
    orbit U (timeIntegral U x a) t = ∫ s in t..t+a, orbit U x s := by
  have integral := (U (Multiplicative.ofAdd t)).toLinearIsometry.intervalIntegral_comp_comm
    (a := 0) (b := a) (μ := volume) (orbit U x)
  have transform : (fun s => (U (Multiplicative.ofAdd t)) (orbit U x s)) =
      fun s => orbit U x (t + s) := by
    funext s
    exact (orbit_add U x t s).symm
  calc
    _ = ∫ s in 0..a, (U (Multiplicative.ofAdd t)) (orbit U x s) := integral.symm
    _ = _ := by
      rw [transform, intervalIntegral.integral_comp_add_left]
      simp [add_comm]

include continuousOrbit

theorem timeIntegral_hasDerivAt (x : E) (a t : ℝ) :
    HasDerivAt (orbit U (timeIntegral U x a))
      (orbit U x (t + a) - orbit U x t) t := by
  have upper := ((continuousOrbit x).integral_hasStrictDerivAt 0 (t + a)).hasDerivAt
    |>.scomp t ((hasDerivAt_id t).add_const a)
  have lower := ((continuousOrbit x).integral_hasStrictDerivAt 0 t).hasDerivAt
  have derivative := upper.sub lower
  convert derivative using 1
  · funext s
    rw [orbit_timeIntegral]
    change (∫ u in s..s+a, orbit U x u) =
      (∫ u in 0..s+a, orbit U x u) - ∫ u in 0..s, orbit U x u
    exact (intervalIntegral.integral_interval_sub_left
      ((continuousOrbit x).intervalIntegrable (μ := volume) 0 (s + a))
      ((continuousOrbit x).intervalIntegrable (μ := volume) 0 s)).symm
  · simp

theorem timeIntegral_mem_domain (x : E) (a : ℝ) : timeIntegral U x a ∈ domain U :=
  (timeIntegral_hasDerivAt U continuousOrbit x a 0).differentiableAt

/-- Rescaling the generated integral supplies the dense approximation. -/
def timeAverage (x : E) (a : ℝ) : E := a⁻¹ • timeIntegral U x a

theorem timeAverage_mem_domain (x : E) (a : ℝ) : timeAverage U x a ∈ domain U := by
  change DifferentiableAt ℝ (orbit U (a⁻¹ • timeIntegral U x a)) 0
  have derivative := (timeIntegral_hasDerivAt U continuousOrbit x a 0).const_smul a⁻¹
  simpa [orbit] using derivative.differentiableAt

theorem timeAverage_tendsto (x : E) :
    Tendsto (timeAverage U x) (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
  have derivative := ((continuousOrbit x).integral_hasStrictDerivAt 0 0).hasDerivAt
  convert derivative.tendsto_slope using 1
  · funext a
    simp [timeAverage, timeIntegral, slope]
  · simp

/-- Strong continuity generates density of the actual derivative domain. -/
theorem domain_dense : Dense (domain U : Set E) := by
  intro x
  exact mem_closure_of_tendsto (timeAverage_tendsto U continuousOrbit x)
    (Eventually.of_forall (timeAverage_mem_domain U continuousOrbit x))

end
end SaturationMonoid.Quantum.Generator
