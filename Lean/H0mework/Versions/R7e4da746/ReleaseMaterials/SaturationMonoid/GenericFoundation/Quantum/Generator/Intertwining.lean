import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Generator.Mapping
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! An isometric time intertwiner preserves the full generator domain.
Its adjoint supplies the converse, including every domain vector. -/

set_option autoImplicit false
open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.Quantum.Generator.Intertwining

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (U : Multiplicative ℝ →* (E ≃ₗᵢ[ℂ] E))
  (V : Multiplicative ℝ →* (F ≃ₗᵢ[ℂ] F)) (I : E →ₗᵢ[ℂ] F)
  (square : ∀ t x, I (U t x) = V t (I x))

include square in
theorem hasDerivAt (x : domain U) :
    HasDerivAt (orbit V (I x.val)) (I (generator U x)) 0 :=
  mapped_derivative U V I.toContinuousLinearMap square x

def domainPoint (x : domain U) : domain V :=
  mappedPoint U V I.toContinuousLinearMap square x

theorem hamiltonian_value (x : domain U) :
    I (hamiltonian U x) = hamiltonian V (domainPoint U V I square x) :=
  (mapped_hamiltonian U V I.toContinuousLinearMap square x).symm

variable [CompleteSpace E] [CompleteSpace F]

include square in
theorem domain_iff (x : E) : I x ∈ domain V ↔ x ∈ domain U := by
  constructor
  · intro hx
    have derivative := (I.toContinuousLinearMap.adjoint.restrictScalars ℝ).differentiableAt.comp 0 hx
    change DifferentiableAt ℝ (orbit U x) 0
    convert! derivative using 1
    funext t
    change U (Multiplicative.ofAdd t) x = I.toContinuousLinearMap.adjoint (V (Multiplicative.ofAdd t) (I x))
    rw [← square]
    exact (congrArg (fun L : E →L[ℂ] E => L (U (Multiplicative.ofAdd t) x)) I.adjoint_comp_self).symm
  · intro hx
    exact (domainPoint U V I square ⟨x, hx⟩).property

end
end SaturationMonoid.Quantum.Generator.Intertwining
