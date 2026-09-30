import H0mework.Physics.LowEnergyFermion.Charge

/-! Fixed-particle CAR words that strictly raise an occupation grade.
The grade comes from a subset of the original one-particle modes.  No
vanishing assumption on the final word is supplied. -/
set_option autoImplicit false
namespace SourceFockRaising
open SaturationMonoid.PhysicsCore
open LowEnergy QuantizationCheck.Fermion
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

abbrev End := Module.End ℂ (Fock ι)

def total : End (ι := ι) := Fermion.occupationCharge (fun _ => 1)
def grade (target : Finset ι) : End (ι := ι) :=
  Fermion.occupationCharge (fun i => if i ∈ target then 1 else 0)

omit [Fintype ι] [LinearOrder ι] in
theorem total_apply (ψ : Fock ι) (s : Finset ι) :
    total ψ s = (s.card : ℂ) * ψ s := by simp [total]

omit [Fintype ι] in
theorem grade_apply (target : Finset ι) (ψ : Fock ι) (s : Finset ι) :
    grade target ψ s = ((s.filter (fun i => i ∈ target)).card : ℂ) * ψ s := by
  simp [grade, Fermion.occupationCharge_apply, Finset.filter_mem_eq_inter]

omit [Fintype ι] in
theorem grade_above_particle_number (target : Finset ι) (N m : ℕ) (too_high : N < m)
    (ψ : Fock ι) (number : total ψ = (N : ℂ) • ψ)
    (weight : grade target ψ = (m : ℂ) • ψ) : ψ = 0 := by
  funext s
  by_contra nonzero
  have nonzero' : ψ s ≠ 0 := nonzero
  have hn : (s.card : ℂ) * ψ s = (N : ℂ) * ψ s := by
    simpa only [total_apply, Pi.smul_apply, smul_eq_mul] using congrFun number s
  have hm : (((s.filter (fun i => i ∈ target)).card : ℕ) : ℂ) * ψ s =
      (m : ℂ) * ψ s := by
    simpa only [grade_apply, Pi.smul_apply, smul_eq_mul] using congrFun weight s
  have hn' : s.card = N := by exact_mod_cast (mul_right_cancel₀ nonzero' hn)
  have hm' : (s.filter (fun i => i ∈ target)).card = m := by
    exact_mod_cast (mul_right_cancel₀ nonzero' hm)
  have bound := Finset.card_filter_le s (fun i => i ∈ target)
  omega

omit [Fintype ι] in
theorem raises_eigenstate (target : Finset ι) (T : End (ι := ι))
    (raises : grade target * T = T * grade target + T)
    (ψ : Fock ι) (m : ℕ) (weight : grade target ψ = (m : ℂ) • ψ) :
    grade target (T ψ) = ((m+1 : ℕ) : ℂ) • T ψ := by
  have law := congrArg (fun A : End (ι := ι) => A ψ) raises
  simp only [Module.End.mul_apply, LinearMap.add_apply, weight, map_smul] at law
  rw [law, Nat.cast_add, Nat.cast_one, add_smul, one_smul]

omit [Fintype ι] in
theorem word_eigenstates (target : Finset ι) (word : List (End (ι := ι)))
    (preserves : ∀ T ∈ word, total * T = T * total)
    (raises : ∀ T ∈ word, grade target * T = T * grade target + T)
    (ψ : Fock ι) (N m : ℕ)
    (number : total ψ = (N : ℂ) • ψ)
    (weight : grade target ψ = (m : ℂ) • ψ) :
    total (word.prod ψ) = (N : ℂ) • word.prod ψ ∧
    grade target (word.prod ψ) = ((m+word.length : ℕ) : ℂ) • word.prod ψ := by
  induction word with
  | nil => simpa using And.intro number weight
  | cons T tail ih =>
    have inner := ih (fun U h => preserves U (List.mem_cons_of_mem T h))
      (fun U h => raises U (List.mem_cons_of_mem T h))
    have first := Fermion.occupationCharge_preserves_eigenstate (fun _ : ι => (1 : ℂ)) T
      (preserves T (List.mem_cons_self)) (tail.prod ψ) (N : ℂ) inner.1
    have second := raises_eigenstate target T (raises T (List.mem_cons_self))
      (tail.prod ψ) (m+tail.length) inner.2
    simpa only [total, List.prod_cons, Module.End.mul_apply, List.length_cons, Nat.add_assoc] using
      And.intro first second

omit [Fintype ι] in
theorem basis_eigenstate (q : ι → ℂ) (s : Finset ι) :
    Fermion.occupationCharge q (occupationBasis s) = (∑ i ∈ s, q i) • occupationBasis s := by
  funext t
  by_cases same : t = s
  · subst t; simp [Fermion.occupationCharge_apply, occupationBasis]
  · simp [Fermion.occupationCharge_apply, occupationBasis, same]

theorem word_vanishes_on_number_sector (target : Finset ι) (word : List (End (ι := ι)))
    (preserves : ∀ T ∈ word, total * T = T * total)
    (raises : ∀ T ∈ word, grade target * T = T * grade target + T)
    (N : ℕ) (long_word : N < word.length)
    (ψ : Fock ι) (sector : ∀ s : Finset ι, s.card ≠ N → ψ s = 0) : word.prod ψ = 0 := by
  have basis_zero (s : Finset ι) (size : s.card = N) : word.prod (occupationBasis s) = 0 := by
    have number : total (occupationBasis s) = (N : ℂ) • occupationBasis s := by
      simpa [total, size] using basis_eigenstate (fun _ : ι => (1 : ℂ)) s
    have weight : grade target (occupationBasis s) =
        (((s.filter (fun i => i ∈ target)).card : ℕ) : ℂ) • occupationBasis s := by
      simpa [grade, Finset.filter_mem_eq_inter] using
        basis_eigenstate (fun i : ι => if i ∈ target then (1 : ℂ) else 0) s
    have state := word_eigenstates target word preserves raises (occupationBasis s) N
      (s.filter (fun i => i ∈ target)).card number weight
    exact grade_above_particle_number target N _ (by omega) _ state.1 state.2
  have expansion : ψ = ∑ s : Finset ι, ψ s • occupationBasis s := by
    funext t
    simp [occupationBasis, Finset.sum_apply]
  rw [expansion, map_sum]
  apply Finset.sum_eq_zero
  intro s _
  rw [map_smul]
  by_cases size : s.card = N
  · rw [basis_zero s size, smul_zero]
  · rw [sector s size, zero_smul]

theorem quantize_preserves_number (A : Matrix ι ι ℂ) :
    total * Fermion.quantize A = Fermion.quantize A * total := by
  exact Fermion.occupationCharge_quantize (fun _ : ι => (1 : ℂ)) A (by intro i j; simp)

theorem quantize_raises_grade (target : Finset ι) (A : Matrix ι ι ℂ)
    (source_grade : ∀ i j, ((if i ∈ target then 1 else 0 : ℂ) -
      (if j ∈ target then 1 else 0 : ℂ) - 1) * A i j = 0) :
    grade target * Fermion.quantize A = Fermion.quantize A * grade target + Fermion.quantize A := by
  simp only [Fermion.quantize, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [grade, Fermion.occupationCharge_bilinear, smul_add, smul_smul]
  have coefficient : A i j * ((if i ∈ target then 1 else 0 : ℂ) -
      (if j ∈ target then 1 else 0 : ℂ)) = A i j := by
    linear_combination source_grade i j
  rw [coefficient]

theorem matrix_word_vanishes_on_number_sector (target : Finset ι)
    (word : List (Matrix ι ι ℂ))
    (source_grade : ∀ A ∈ word, ∀ i j, ((if i ∈ target then 1 else 0 : ℂ) -
      (if j ∈ target then 1 else 0 : ℂ) - 1) * A i j = 0)
    (N : ℕ) (long_word : N < word.length)
    (ψ : Fock ι) (sector : ∀ s : Finset ι, s.card ≠ N → ψ s = 0) :
    (word.map Fermion.quantize).prod ψ = 0 := by
  apply word_vanishes_on_number_sector target (word.map Fermion.quantize) _ _ N
    (by simpa using long_word) ψ sector
  · intro T member
    obtain ⟨A, _, rfl⟩ := List.mem_map.mp member
    exact quantize_preserves_number A
  · intro T member
    obtain ⟨A, belongs, rfl⟩ := List.mem_map.mp member
    exact quantize_raises_grade target A (source_grade A belongs)

end
end SourceFockRaising
