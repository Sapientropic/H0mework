import H0mework.Quantum.Generator.Core
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The same flow generates translated domain witnesses and transports its
actual derivative. Differentiating the preserved inner product makes that
generator skew symmetric and its physical Hamiltonian symmetric. -/

set_option autoImplicit false

open scoped InnerProductSpace

namespace SaturationMonoid.Quantum.Generator

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (U : Multiplicative ℝ →* (E ≃ₗᵢ[ℂ] E))

theorem translated_hasDerivAt (x : domain U) (t : ℝ) :
    HasDerivAt (orbit U (orbit U x t)) (orbit U (generator U x) t) 0 := by
  have translated := (orbit_hasDerivAt U x t).scomp_of_eq 0
    ((hasDerivAt_id 0).add_const t) (zero_add t).symm
  convert translated using 1
  · funext s
    exact (orbit_add U x s t).symm
  · simp

theorem orbit_mem_domain (x : domain U) (t : ℝ) : orbit U x t ∈ domain U :=
  (translated_hasDerivAt U x t).differentiableAt

def domainOrbit (x : domain U) (t : ℝ) : domain U :=
  ⟨orbit U x t, orbit_mem_domain U x t⟩

theorem generator_domainOrbit (x : domain U) (t : ℝ) :
    generator U (domainOrbit U x t) = orbit U (generator U x) t :=
  (translated_hasDerivAt U x t).deriv

theorem hamiltonian_domainOrbit (x : domain U) (t : ℝ) :
    hamiltonian U (domainOrbit U x t) = orbit U (hamiltonian U x) t := by
  change Complex.I • generator U (domainOrbit U x t) =
    orbit U (Complex.I • generator U x) t
  rw [generator_domainOrbit, map_smul]
  rfl

theorem generator_skewSymmetric (x y : domain U) :
    ⟪generator U x, (y : E)⟫_ℂ = -⟪(x : E), generator U y⟫_ℂ := by
  have differentiated := (hasDerivAt_zero U x).inner ℂ (hasDerivAt_zero U y)
  have constant : (fun t : ℝ => ⟪orbit U x t, orbit U y t⟫_ℂ) =
      fun _ => ⟪(x : E), (y : E)⟫_ℂ := by
    funext t
    exact (U (Multiplicative.ofAdd t)).inner_map_map x y
  rw [constant] at differentiated
  have equation := differentiated.unique (hasDerivAt_const 0 ⟪(x : E), (y : E)⟫_ℂ)
  simp only [orbit_zero] at equation
  exact eq_neg_of_add_eq_zero_right equation

theorem hamiltonian_symmetric (x y : domain U) :
    ⟪hamiltonian U x, (y : E)⟫_ℂ = ⟪(x : E), hamiltonian U y⟫_ℂ := by
  change ⟪Complex.I • generator U x, (y : E)⟫_ℂ =
    ⟪(x : E), Complex.I • generator U y⟫_ℂ
  rw [inner_smul_left, inner_smul_right, generator_skewSymmetric]
  simp

end
end SaturationMonoid.Quantum.Generator
