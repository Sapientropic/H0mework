import H0mework.Physics.LowEnergy.Quantum.FockRaising
import Mathlib.RingTheory.TensorProduct.Maps

/-! The fixed-particle termination law with ordered, noncommuting boson factors.
Every factor acts on the stated common algebraic domain. No exchange of
time-ordered boson factors and no analytic Dyson convergence is assumed. -/
set_option autoImplicit false
namespace SourceFockRaising
open SaturationMonoid.PhysicsCore
open LowEnergy QuantizationCheck.Fermion
open scoped TensorProduct
noncomputable section
variable {ι V : Type*} [Fintype ι] [LinearOrder ι]
variable [AddCommGroup V] [Module ℂ V]

omit [Fintype ι] [LinearOrder ι] in
theorem ordered_tensor_product (word : List (Module.End ℂ V × End (ι := ι))) :
    (word.map (fun pair => pair.1 ⊗ₜ[ℂ] pair.2)).prod =
      (word.map Prod.fst).prod ⊗ₜ[ℂ] (word.map Prod.snd).prod := by
  induction word with
  | nil => rfl
  | cons pair tail ih =>
    simp only [List.map_cons, List.prod_cons, ih, Algebra.TensorProduct.tmul_mul_tmul]

theorem tensor_word_vanishes_on_number_sector (target : Finset ι)
    (word : List (Module.End ℂ V × Matrix ι ι ℂ))
    (source_grade : ∀ pair ∈ word, ∀ i j, ((if i ∈ target then 1 else 0 : ℂ) -
      (if j ∈ target then 1 else 0 : ℂ) - 1) * pair.2 i j = 0)
    (N : ℕ) (long_word : N < word.length)
    (ψ : Fock ι) (sector : ∀ s : Finset ι, s.card ≠ N → ψ s = 0) (v : V) :
    Module.endTensorEndAlgHom (S := ℂ)
      (word.map (fun pair => pair.1 ⊗ₜ[ℂ] Fermion.quantize pair.2)).prod
      (v ⊗ₜ[ℂ] ψ) = 0 := by
  have factor := ordered_tensor_product
    (word.map (fun pair => (pair.1, Fermion.quantize pair.2)))
  simp only [List.map_map, Function.comp_def] at factor
  rw [factor]
  simp only [Module.endTensorEndAlgHom_apply, TensorProduct.AlgebraTensorModule.map_tmul]
  have grade (A : Matrix ι ι ℂ) (member : A ∈ word.map Prod.snd) :
      ∀ i j, ((if i ∈ target then 1 else 0 : ℂ) -
        (if j ∈ target then 1 else 0 : ℂ) - 1) * A i j = 0 := by
    obtain ⟨pair, belongs, rfl⟩ := List.mem_map.mp member
    exact source_grade pair belongs
  have vanish := matrix_word_vanishes_on_number_sector target (word.map Prod.snd) grade N
    (by simpa using long_word) ψ sector
  simp only [List.map_map, Function.comp_def] at vanish
  rw [vanish, TensorProduct.tmul_zero]

end
end SourceFockRaising
