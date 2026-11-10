import H0mework.Quantum.Generator.Core

/-! An actual bounded orbit intertwiner transports differentiability and
its Hamiltonian value by the existing chain rule. -/

set_option autoImplicit false

namespace SaturationMonoid.Quantum.Generator.Intertwining

noncomputable section

theorem mapped_derivative {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (U : Multiplicative ℝ →* (E ≃ₗᵢ[ℂ] E)) (V : Multiplicative ℝ →* (F ≃ₗᵢ[ℂ] F))
    (L : E →L[ℂ] F) (square : ∀ t x, L (U t x) = V t (L x)) (x : Quantum.Generator.domain U) :
    HasDerivAt (Quantum.Generator.orbit V (L x.val)) (L (Quantum.Generator.generator U x)) 0 := by
  have derivative := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (Quantum.Generator.hasDerivAt_zero U x)
  convert! derivative using 1
  funext t
  exact (square (Multiplicative.ofAdd t) x.val).symm

def mappedPoint {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (U : Multiplicative ℝ →* (E ≃ₗᵢ[ℂ] E)) (V : Multiplicative ℝ →* (F ≃ₗᵢ[ℂ] F))
    (L : E →L[ℂ] F) (square : ∀ t x, L (U t x) = V t (L x))
    (x : Quantum.Generator.domain U) : Quantum.Generator.domain V :=
  ⟨L x.val, (mapped_derivative U V L square x).differentiableAt⟩

theorem mapped_hamiltonian {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (U : Multiplicative ℝ →* (E ≃ₗᵢ[ℂ] E)) (V : Multiplicative ℝ →* (F ≃ₗᵢ[ℂ] F))
    (L : E →L[ℂ] F) (square : ∀ t x, L (U t x) = V t (L x)) (x : Quantum.Generator.domain U) :
    Quantum.Generator.hamiltonian V (mappedPoint U V L square x) = L (Quantum.Generator.hamiltonian U x) := by
  change Complex.I • deriv (Quantum.Generator.orbit V (L x.val)) 0 =
    L (Complex.I • Quantum.Generator.generator U x)
  rw [(mapped_derivative U V L square x).deriv, map_smul]

end
end SaturationMonoid.Quantum.Generator.Intertwining
