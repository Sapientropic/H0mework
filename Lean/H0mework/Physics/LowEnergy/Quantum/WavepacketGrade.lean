import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-! Bounded occupation grades on an arbitrary configuration space.
No finiteness of momentum or of the configuration space is assumed. -/
set_option autoImplicit false
namespace SourceWavepacketGrade
open scoped BigOperators
noncomputable section
variable {Ω B : Type*} [AddCommGroup B] [Module ℂ B]

def grade (weight : Ω → ℕ) : Module.End ℂ (Ω → B) where
  toFun f x := (weight x : ℂ) • f x
  map_add' f g := by ext x; simp [smul_add]
  map_smul' c f := by
    ext x
    exact smul_comm (weight x : ℂ) c (f x)

@[simp] theorem grade_apply (weight : Ω → ℕ) (f : Ω → B) (x : Ω) :
    grade weight f x = (weight x : ℂ) • f x := rfl

def project (weight : Ω → ℕ) (n : ℕ) (f : Ω → B) : Ω → B :=
  fun x => if weight x = n then f x else 0

theorem project_eigenstate (weight : Ω → ℕ) (n : ℕ) (f : Ω → B) :
    grade weight (project weight n f) = (n : ℂ) • project weight n f := by
  funext x
  by_cases same : weight x = n <;> simp [project, same]

omit [Module ℂ B] in
theorem finite_grade_decomposition (weight : Ω → ℕ) (N : ℕ)
    (bound : ∀ x, weight x ≤ N) (f : Ω → B) :
    f = ∑ n ∈ Finset.range (N+1), project weight n f := by
  funext x
  simp only [Finset.sum_apply, project]
  rw [Finset.sum_eq_single (weight x)]
  · simp
  · intro n _ different
    exact if_neg (Ne.symm different)
  · intro absent
    exact (absent (Finset.mem_range.mpr (by have := bound x; omega))).elim

theorem eigenstate_above_bound (weight : Ω → ℕ) (N m : ℕ)
    (bound : ∀ x, weight x ≤ N) (high : N < m)
    (f : Ω → B) (state : grade weight f = (m : ℂ) • f) : f = 0 := by
  funext x
  have scalar_nonzero : ((weight x : ℂ) - (m : ℂ)) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (show weight x ≠ m by have := bound x; omega)
  have equality : ((weight x : ℂ) - (m : ℂ)) • f x = 0 := by
    have value := congrFun state x
    simpa only [grade_apply, Pi.smul_apply, sub_smul, sub_eq_zero] using value
  exact (smul_eq_zero.mp equality).resolve_left scalar_nonzero

theorem raise_eigenstate (weight : Ω → ℕ) (T : Module.End ℂ (Ω → B))
    (law : grade weight * T = T * grade weight + T)
    (f : Ω → B) (n : ℕ) (state : grade weight f = (n : ℂ) • f) :
    grade weight (T f) = ((n+1 : ℕ) : ℂ) • T f := by
  have value := congrArg (fun A : Module.End ℂ (Ω → B) => A f) law
  simp only [Module.End.mul_apply, LinearMap.add_apply, state, map_smul] at value
  rw [value, Nat.cast_add, Nat.cast_one, add_smul, one_smul]

theorem word_eigenstate (weight : Ω → ℕ) (word : List (Module.End ℂ (Ω → B)))
    (raises : ∀ T ∈ word, grade weight * T = T * grade weight + T)
    (f : Ω → B) (n : ℕ) (state : grade weight f = (n : ℂ) • f) :
    grade weight (word.prod f) = ((n+word.length : ℕ) : ℂ) • word.prod f := by
  induction word with
  | nil => simpa using state
  | cons T tail ih =>
    have inner := ih (fun U h => raises U (List.mem_cons_of_mem T h))
    simpa only [List.prod_cons, Module.End.mul_apply, List.length_cons, Nat.add_assoc] using
      raise_eigenstate weight T (raises T List.mem_cons_self) (tail.prod f) (n+tail.length) inner

theorem bounded_grade_word_zero (weight : Ω → ℕ) (N : ℕ)
    (bound : ∀ x, weight x ≤ N) (word : List (Module.End ℂ (Ω → B)))
    (raises : ∀ T ∈ word, grade weight * T = T * grade weight + T)
    (long_word : N < word.length) : word.prod = 0 := by
  apply LinearMap.ext
  intro f
  have each (n : ℕ) : word.prod (project weight n f) = 0 := by
    apply eigenstate_above_bound weight N (n+word.length) bound (by omega)
    exact word_eigenstate weight word raises _ n (project_eigenstate weight n f)
  rw [finite_grade_decomposition weight N bound f, map_sum]
  simp only [each, Finset.sum_const_zero, LinearMap.zero_apply]

end
end SourceWavepacketGrade
