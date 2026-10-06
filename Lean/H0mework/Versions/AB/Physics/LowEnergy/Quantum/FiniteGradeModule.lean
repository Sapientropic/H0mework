import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! Finite spectral resolution pays varying raising words on the entire module. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.FiniteGradeModule
open scoped BigOperators
variable {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]

theorem raises_eigenvalue (G T : Module.End ℂ V) (raises : G*T=T*G+T)
    (x : V) (c : ℂ) (eigen : G x=c • x) : G (T x)=(c+1) • T x := by
  have h := congrArg (fun A : Module.End ℂ V => A x) raises
  simp only [Module.End.mul_apply, LinearMap.add_apply, eigen, map_smul] at h
  rw [h, add_smul, one_smul]

theorem word_eigenvalue (G : Module.End ℂ V) (word : List (Module.End ℂ V))
    (laws : ∀ T ∈ word, G*T=T*G+T) (x : V) (c : ℂ) (eigen : G x=c • x) :
    G (word.prod x)=(c+(word.length : ℂ)) • word.prod x := by
  induction word with
  | nil => simpa using eigen
  | cons T tail ih =>
      have htail := ih (fun A hA => laws A (List.mem_cons_of_mem T hA))
      have h := raises_eigenvalue G T (laws T (List.mem_cons_self)) (tail.prod x)
        (c+(tail.length : ℂ)) htail
      simpa only [List.prod_cons, Module.End.mul_apply, List.length_cons, Nat.cast_add,
        Nat.cast_one, add_assoc] using h

theorem above_spectrum (G : Module.End ℂ V) (P : ι → Module.End ℂ V) (w : ι → ℤ)
    (resolution : ∑ i, P i=1) (left : ∀ i, P i*G=(w i : ℂ) • P i)
    (x : V) (k : ℤ) (eigen : G x=(k : ℂ) • x) (above : ∀ i, w i<k) : x=0 := by
  have hp (i : ι) : P i x=0 := by
    have h := congrArg (fun A : Module.End ℂ V => A x) (left i)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, eigen, map_smul] at h
    have hz : ((w i : ℂ)-(k : ℂ)) • P i x=0 := by rw [sub_smul, ← h, sub_self]
    have hc : (w i : ℂ)-(k : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_lt (above i)))
    exact (smul_eq_zero.mp hz).resolve_left hc
  have h := congrArg (fun A : Module.End ℂ V => A x) resolution
  simpa only [LinearMap.sum_apply, hp, Finset.sum_const_zero, Module.End.one_apply] using h.symm

theorem word_zero (G : Module.End ℂ V) (P : ι → Module.End ℂ V) (w : ι → ℤ)
    (resolution : ∑ i, P i=1) (left : ∀ i, P i*G=(w i : ℂ) • P i)
    (right : ∀ i, G*P i=(w i : ℂ) • P i) (lower upper : ℤ)
    (bounds : ∀ i, lower ≤ w i ∧ w i ≤ upper) (word : List (Module.End ℂ V))
    (laws : ∀ T ∈ word, G*T=T*G+T) (long : upper-lower < (word.length : ℤ)) : word.prod=0 := by
  apply LinearMap.ext
  intro x
  have hp (i : ι) : word.prod (P i x)=0 := by
    apply above_spectrum G P w resolution left _ (w i+(word.length : ℤ))
    · have he := congrArg (fun A : Module.End ℂ V => A x) (right i)
      have h := word_eigenvalue G word laws (P i x) (w i : ℂ) he
      simpa only [Int.cast_add, Int.cast_natCast] using h
    · intro j
      have hi := (bounds i).1
      have hj := (bounds j).2
      omega
  have hx : ∑ i, P i x=x := by
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using
      congrArg (fun A : Module.End ℂ V => A x) resolution
  rw [← hx, map_sum]
  exact Finset.sum_eq_zero (fun i _ => hp i)

#print axioms word_zero
end LowEnergy.FiniteGradeModule
