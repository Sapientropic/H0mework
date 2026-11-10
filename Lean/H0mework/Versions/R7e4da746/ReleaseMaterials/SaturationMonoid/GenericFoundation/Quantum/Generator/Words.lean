import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Generator.Commutator

/-! The existing ordered-product derivative is shared by source field
families. Multiplication order is retained in each Leibniz term. -/

set_option autoImplicit false

namespace SaturationMonoid.Quantum.Generator.Commutator
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def orderedDerivative : List ((H →L[ℂ] H) × (H →L[ℂ] H)) → H →L[ℂ] H
  | [] => 0
  | (A, D) :: rest => D * (rest.map Prod.fst).prod + A * orderedDerivative rest

theorem product_derivative (U : Multiplicative ℝ →* (H ≃ₗᵢ[ℂ] H))
    (letters : List ((H →L[ℂ] H) × (H →L[ℂ] H)))
    (derivatives : ∀ pair ∈ letters, HasDerivAt (conjugation U pair.1) pair.2 0) :
    HasDerivAt (conjugation U (letters.map Prod.fst).prod) (orderedDerivative letters) 0 := by
  induction letters with
  | nil =>
      have same : conjugation U (1 : H →L[ℂ] H) = fun _ : ℝ => 1 := by
        funext t
        exact map_one ((U (Multiplicative.ofAdd t)).conjStarAlgEquiv)
      simpa only [List.map_nil, List.prod_nil, orderedDerivative, same] using
        hasDerivAt_const (0 : ℝ) (1 : H →L[ℂ] H)
  | cons pair rest ih =>
      have first := derivatives pair (by simp)
      have remaining := ih (fun pair hp => derivatives pair (by simp [hp]))
      have generated := first.mul remaining
      convert! generated using 1
      · funext t
        simp [conjugation]
      · simp [orderedDerivative, conjugation_zero]

end
end SaturationMonoid.Quantum.Generator.Commutator
