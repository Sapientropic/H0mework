import H0mework.Quantum.Generator.Averages
import H0mework.Quantum.Generator.Invariance

/-!
# Weak generator equations generate strong orbit derivatives

Testing against the dense derivative domain converts a weak generator
equation into the actual vector-valued orbit integral. The fundamental
theorem of calculus then supplies the strong derivative of the tested vector.
This is the domain-maximality step used by the self-adjointness consumer.
-/

set_option autoImplicit false

open scoped Topology InnerProductSpace
open Filter MeasureTheory

namespace SaturationMonoid.Quantum.Generator

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (U : Multiplicative ℝ →* (E ≃ₗᵢ[ℂ] E))
  (continuousOrbit : ∀ x, Continuous (orbit U x))

theorem inner_orbit_right (x y : E) (t : ℝ) :
    ⟪x, orbit U y t⟫_ℂ = ⟪orbit U x (-t), y⟫_ℂ := by
  have same := (U (Multiplicative.ofAdd t)).inner_map_map (orbit U x (-t)) y
  change ⟪orbit U (orbit U x (-t)) t, orbit U y t⟫_ℂ = _ at same
  simpa only [← orbit_add, add_neg_cancel, orbit_zero] using same

theorem weak_scalar_derivative (y z : E)
    (weak : ∀ x : domain U, ⟪generator U x, y⟫_ℂ = -⟪(x : E), z⟫_ℂ)
    (x : domain U) (t : ℝ) :
    HasDerivAt (fun s => ⟪(x : E), orbit U y s⟫_ℂ) ⟪(x : E), orbit U z t⟫_ℂ t := by
  have reversed := (orbit_hasDerivAt U x (-t)).scomp t (hasDerivAt_neg t)
  have paired := reversed.inner ℂ (hasDerivAt_const t y)
  have relation := weak (domainOrbit U x (-t))
  rw [generator_domainOrbit] at relation
  convert! paired using 1
  · funext s
    exact inner_orbit_right U x y s
  · simp only [neg_smul, one_smul, inner_neg_left, inner_zero_right, zero_add]
    rw [relation, neg_neg, inner_orbit_right]
    rfl

variable [CompleteSpace E]

include continuousOrbit

/-- Dense source tests determine the entire orbit integral, not just scalars. -/
theorem weak_orbit_integral (y z : E)
    (weak : ∀ x : domain U, ⟪generator U x, y⟫_ℂ = -⟪(x : E), z⟫_ℂ) (t : ℝ) :
    orbit U y t - y = timeIntegral U z t := by
  apply (domain_dense U continuousOrbit).eq_of_inner_right ℂ
  intro x hx
  have continuousPair : Continuous (fun s => ⟪x, orbit U z s⟫_ℂ) :=
    continuous_const.inner (continuousOrbit z)
  have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => weak_scalar_derivative U y z weak ⟨x, hx⟩ s)
    (continuousPair.intervalIntegrable (μ := volume) 0 t)
  have integral := (innerSL ℂ x).intervalIntegral_comp_comm
    ((continuousOrbit z).intervalIntegrable (μ := volume) 0 t)
  rw [inner_sub_right]
  calc
    _ = ∫ s in 0..t, ⟪x, orbit U z s⟫_ℂ := by simpa only [orbit_zero] using ftc.symm
    _ = _ := integral

/-- A weak generator witness forces membership in the actual derivative domain. -/
theorem orbit_hasDerivAt_of_weak (y z : E)
    (weak : ∀ x : domain U, ⟪generator U x, y⟫_ℂ = -⟪(x : E), z⟫_ℂ) :
    HasDerivAt (orbit U y) z 0 := by
  have derivative := ((continuousOrbit z).integral_hasStrictDerivAt 0 0).hasDerivAt
    |>.const_add y
  convert derivative using 1
  · funext t
    change orbit U y t = y + timeIntegral U z t
    rw [← weak_orbit_integral U continuousOrbit y z weak t]
    abel
  · simp

end
end SaturationMonoid.Quantum.Generator
