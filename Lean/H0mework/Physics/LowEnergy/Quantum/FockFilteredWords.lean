import H0mework.Physics.LowEnergy.Quantum.FockRaisingTensor

/-! Occupation-filtered words of the complete algebraic Hamiltonian.
Grade-preserving factors may occur between any raising factors. The bound
counts their total source grade, retaining all boson factors in order. -/
set_option autoImplicit false
namespace SourceFockFilteredWords
open SaturationMonoid.PhysicsCore
open LowEnergy QuantizationCheck.Fermion SourceFockRaising
open scoped BigOperators TensorProduct
noncomputable section
variable {ι V : Type*} [Fintype ι] [LinearOrder ι]

def weight (word : List (ℕ × End (ι := ι))) : ℕ := (word.map Prod.fst).sum

omit [Fintype ι] in
theorem homogeneous_eigenstate (target : Finset ι) (T : End (ι := ι)) (w : ℕ)
    (law : grade target * T = T * grade target + (w : ℂ) • T)
    (ψ : Fock ι) (m : ℕ) (eigen : grade target ψ = (m : ℂ) • ψ) :
    grade target (T ψ) = ((m+w : ℕ) : ℂ) • T ψ := by
  have value := congrArg (fun A : End (ι := ι) => A ψ) law
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    eigen, map_smul] at value
  rw [value, Nat.cast_add, add_smul]

omit [Fintype ι] in
theorem word_eigenstate (target : Finset ι) (word : List (ℕ × End (ι := ι)))
    (number_law : ∀ p ∈ word, total * p.2 = p.2 * total)
    (grade_law : ∀ p ∈ word, grade target * p.2 = p.2 * grade target + (p.1 : ℂ) • p.2)
    (ψ : Fock ι) (N m : ℕ)
    (number : total ψ = (N : ℂ) • ψ) (eigen : grade target ψ = (m : ℂ) • ψ) :
    total ((word.map Prod.snd).prod ψ) = (N : ℂ) • (word.map Prod.snd).prod ψ ∧
    grade target ((word.map Prod.snd).prod ψ) = ((m+weight word : ℕ) : ℂ) • (word.map Prod.snd).prod ψ := by
  induction word with
  | nil => simpa [weight] using And.intro number eigen
  | cons p tail ih =>
    have inner := ih (fun q h => number_law q (List.mem_cons_of_mem p h))
      (fun q h => grade_law q (List.mem_cons_of_mem p h))
    have hn := Fermion.occupationCharge_preserves_eigenstate (fun _ : ι => (1 : ℂ)) p.2
      (number_law p (List.mem_cons_self)) ((tail.map Prod.snd).prod ψ) (N : ℂ) inner.1
    have hg := homogeneous_eigenstate target p.2 p.1 (grade_law p (List.mem_cons_self))
      ((tail.map Prod.snd).prod ψ) (m+weight tail) inner.2
    simpa [weight, total, List.map_cons, List.prod_cons, Module.End.mul_apply,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using And.intro hn hg

theorem weighted_word_vanishes (target : Finset ι) (word : List (ℕ × End (ι := ι)))
    (number_law : ∀ p ∈ word, total * p.2 = p.2 * total)
    (grade_law : ∀ p ∈ word, grade target * p.2 = p.2 * grade target + (p.1 : ℂ) • p.2)
    (N : ℕ) (too_many_raises : N < weight word)
    (ψ : Fock ι) (sector : ∀ s : Finset ι, s.card ≠ N → ψ s = 0) :
    (word.map Prod.snd).prod ψ = 0 := by
  have basis_zero (s : Finset ι) (size : s.card = N) :
      (word.map Prod.snd).prod (occupationBasis s) = 0 := by
    have hn : total (occupationBasis s) = (N : ℂ) • occupationBasis s := by
      simpa [total, size] using basis_eigenstate (fun _ : ι => (1 : ℂ)) s
    have hg : grade target (occupationBasis s) =
        (((s.filter (fun i => i ∈ target)).card : ℕ) : ℂ) • occupationBasis s := by
      simpa [grade, Finset.filter_mem_eq_inter] using
        basis_eigenstate (fun i : ι => if i ∈ target then (1 : ℂ) else 0) s
    have state := word_eigenstate target word number_law grade_law (occupationBasis s) N
      (s.filter (fun i => i ∈ target)).card hn hg
    exact grade_above_particle_number target N _ (by omega) _ state.1 state.2
  have expansion : ψ = ∑ s : Finset ι, ψ s • occupationBasis s := by
    funext t
    simp [occupationBasis, Finset.sum_apply]
  rw [expansion, map_sum]
  apply Finset.sum_eq_zero
  intro s _
  rw [map_smul]
  by_cases same : s.card = N
  · rw [basis_zero s same, smul_zero]
  · rw [sector s same, zero_smul]

theorem weighted_tensor_word_vanishes [AddCommGroup V] [Module ℂ V]
    (target : Finset ι) (word : List (ℕ × (Module.End ℂ V × End (ι := ι))))
    (number_law : ∀ p ∈ word, total * p.2.2 = p.2.2 * total)
    (grade_law : ∀ p ∈ word, grade target * p.2.2 = p.2.2 * grade target + (p.1 : ℂ) • p.2.2)
    (N : ℕ) (too_many_raises : N < (word.map Prod.fst).sum)
    (ψ : Fock ι) (sector : ∀ s : Finset ι, s.card ≠ N → ψ s = 0) (v : V) :
    Module.endTensorEndAlgHom (S := ℂ)
      (word.map (fun p => p.2.1 ⊗ₜ[ℂ] p.2.2)).prod (v ⊗ₜ[ℂ] ψ) = 0 := by
  have factor := ordered_tensor_product (word.map Prod.snd)
  simp only [List.map_map, Function.comp_def] at factor
  rw [factor]
  simp only [Module.endTensorEndAlgHom_apply, TensorProduct.AlgebraTensorModule.map_tmul]
  have vanish := weighted_word_vanishes target (word.map (fun p => (p.1, p.2.2)))
    (by intro p h; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h; exact number_law q hq)
    (by intro p h; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h; exact grade_law q hq)
    N (by simpa [weight, List.map_map, Function.comp_def] using too_many_raises) ψ sector
  simp only [List.map_map, Function.comp_def] at vanish
  rw [vanish, TensorProduct.tmul_zero]

end
end SourceFockFilteredWords
