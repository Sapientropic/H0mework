import H0mework.Physics.LowEnergy.Quantum.WavepacketGrade
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.GroupTheory.Perm.Sign

/-! Particle-line insertions on a genuine N-body configuration space.
Momentum is arbitrary and need not be finite; separate lines may carry the
same internal label. Operator-valued coefficients retain their order. -/
set_option autoImplicit false
namespace SourceWavepacketInteraction
open scoped BigOperators
noncomputable section
variable {M I B : Type*} [Fintype I] [DecidableEq I]
variable [AddCommGroup B] [Module ℂ B] {N : ℕ}

abbrev Configuration (M I : Type*) (N : ℕ) := Fin N → M × I
abbrev Wave (M I B : Type*) (N : ℕ) := Configuration M I N → B

def occupation (target : Finset I) (x : Configuration M I N) : ℕ :=
  ∑ line : Fin N, if (x line).2 ∈ target then 1 else 0

omit [Fintype I] in
theorem occupation_bound (target : Finset I) (x : Configuration M I N) :
    occupation target x ≤ N := by
  calc
    _ ≤ ∑ _line : Fin N, 1 := Finset.sum_le_sum (by intro line _; split <;> omega)
    _ = N := by simp

omit [Fintype I] in
theorem occupation_update (target : Finset I) (x : Configuration M I N)
    (line : Fin N) (momentum : M) (j : I)
    (outgoing : (x line).2 ∈ target) (incoming : j ∉ target) :
    occupation target (Function.update x line (momentum, j)) + 1 = occupation target x := by
  let f : Fin N → ℕ := fun i => if (x i).2 ∈ target then 1 else 0
  have updated : (fun i : Fin N => if ((Function.update x line (momentum, j)) i).2 ∈ target
      then (1 : ℕ) else 0) = Function.update f line 0 := by
    funext i
    by_cases same : i = line
    · subst i; simp [incoming]
    · simp [Function.update_of_ne same, f]
  rw [occupation, updated, Finset.sum_update_of_mem (Finset.mem_univ line)]
  have old := Finset.sum_erase_add Finset.univ f (Finset.mem_univ line)
  simpa [occupation, f, outgoing, Finset.sdiff_singleton_eq_erase] using old

def lineAction (shift : M → M) (kernel : M → I → I → Module.End ℂ B)
    (line : Fin N) : Module.End ℂ (Wave M I B N) where
  toFun ψ x := ∑ j : I, kernel (x line).1 (x line).2 j
    (ψ (Function.update x line (shift (x line).1, j)))
  map_add' ψ φ := by ext x; simp [map_add, Finset.sum_add_distrib]
  map_smul' c ψ := by ext x; simp [map_smul, Finset.smul_sum]

def interaction (shift : M → M) (kernel : M → I → I → Module.End ℂ B) :
    Module.End ℂ (Wave M I B N) := ∑ line : Fin N, lineAction shift kernel line

theorem line_raises_occupation (target : Finset I)
    (shift : M → M) (kernel : M → I → I → Module.End ℂ B)
    (source_support : ∀ p i j, kernel p i j ≠ 0 → i ∈ target ∧ j ∉ target)
    (line : Fin N) :
    SourceWavepacketGrade.grade (occupation target) * lineAction shift kernel line =
      lineAction shift kernel line * SourceWavepacketGrade.grade (occupation target) +
        lineAction shift kernel line := by
  apply LinearMap.ext
  intro ψ
  funext x
  simp only [Module.End.mul_apply, LinearMap.add_apply, Pi.add_apply, SourceWavepacketGrade.grade_apply,
    lineAction, LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum, map_smul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases empty : kernel (x line).1 (x line).2 j = 0
  · simp [empty]
  · have supported := source_support (x line).1 (x line).2 j empty
    rw [← occupation_update target x line (shift (x line).1) j supported.1 supported.2,
      Nat.cast_add, Nat.cast_one, add_smul, one_smul]

theorem interaction_raises_occupation (target : Finset I)
    (shift : M → M) (kernel : M → I → I → Module.End ℂ B)
    (source_support : ∀ p i j, kernel p i j ≠ 0 → i ∈ target ∧ j ∉ target) :
    SourceWavepacketGrade.grade (occupation target) * interaction (N := N) shift kernel =
      interaction shift kernel * SourceWavepacketGrade.grade (occupation target) +
        interaction shift kernel := by
  simp only [interaction, Finset.mul_sum, Finset.sum_mul,
    line_raises_occupation target shift kernel source_support, Finset.sum_add_distrib]

theorem ordered_wavepacket_word_zero (target : Finset I)
    (shifts : ℕ → M → M) (kernels : ℕ → M → I → I → Module.End ℂ B)
    (source_support : ∀ a p i j, kernels a p i j ≠ 0 → i ∈ target ∧ j ∉ target)
    (word : List ℕ) (long_word : N < word.length) :
    (word.map (fun a => interaction (N := N) (shifts a) (kernels a))).prod = 0 := by
  apply SourceWavepacketGrade.bounded_grade_word_zero (occupation target) N
    (occupation_bound target) _ _ (by simpa using long_word)
  intro T member
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp member
  exact interaction_raises_occupation target (shifts a) (kernels a) (source_support a)

def permute (e : Equiv.Perm (Fin N)) : Module.End ℂ (Wave M I B N) where
  toFun ψ x := ψ (x ∘ e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq I] in
theorem line_permutation (shift : M → M) (kernel : M → I → I → Module.End ℂ B)
    (e : Equiv.Perm (Fin N)) (line : Fin N) :
    lineAction shift kernel (e line) * permute e =
      permute e * lineAction shift kernel line := by
  apply LinearMap.ext
  intro ψ
  funext x
  change (∑ j : I, kernel (x (e line)).1 (x (e line)).2 j
    (ψ ((Function.update x (e line) (shift (x (e line)).1, j)) ∘ e))) =
      ∑ j : I, kernel ((x ∘ e) line).1 ((x ∘ e) line).2 j
        (ψ (Function.update (x ∘ e) line (shift ((x ∘ e) line).1, j)))
  simp_rw [Function.update_comp_eq_of_injective x e.injective]
  rfl

omit [DecidableEq I] in
theorem interaction_permutation (shift : M → M)
    (kernel : M → I → I → Module.End ℂ B) (e : Equiv.Perm (Fin N)) :
    interaction shift kernel * permute e = permute e * interaction shift kernel := by
  simp only [interaction, Finset.sum_mul, Finset.mul_sum]
  rw [← Equiv.sum_comp e (fun line : Fin N => lineAction shift kernel line * permute e)]
  apply Finset.sum_congr rfl
  intro line _
  exact line_permutation shift kernel e line

def Alternating (ψ : Wave M I B N) : Prop :=
  ∀ e : Equiv.Perm (Fin N), permute e ψ = (((Equiv.Perm.sign e : ℤˣ) : ℤ) : ℂ) • ψ

omit [DecidableEq I] in
theorem interaction_preserves_alternating (shift : M → M)
    (kernel : M → I → I → Module.End ℂ B) (ψ : Wave M I B N)
    (fermionic : Alternating ψ) : Alternating (interaction shift kernel ψ) := by
  intro e
  have law := congrArg (fun T : Module.End ℂ (Wave M I B N) => T ψ)
    (interaction_permutation shift kernel e)
  simp only [Module.End.mul_apply] at law
  rw [← law, fermionic e, map_smul]

def scalarKernel (W : M → Matrix I I ℂ) (Q : Module.End ℂ B) :
    M → I → I → Module.End ℂ B := fun p i j => W p i j • Q

omit [Fintype I] in
theorem scalarKernel_support (target : Finset I) (W : M → Matrix I I ℂ)
    (Q : Module.End ℂ B)
    (source_grade : ∀ p i j, ((if i ∈ target then 1 else 0 : ℂ) -
      (if j ∈ target then 1 else 0 : ℂ) - 1) * W p i j = 0) :
    ∀ p i j, scalarKernel W Q p i j ≠ 0 → i ∈ target ∧ j ∉ target := by
  intro p i j nonzero
  have coefficient : W p i j ≠ 0 := by
    intro empty
    exact nonzero (by simp [scalarKernel, empty])
  have native := source_grade p i j
  by_cases hi : i ∈ target <;> by_cases hj : j ∈ target
  · simp [hi, hj] at native
    exact (coefficient native).elim
  · exact ⟨hi, hj⟩
  · simp [hi, hj] at native
    rcases native with contradiction | contradiction
    · norm_num at contradiction
    · exact (coefficient contradiction).elim
  · simp [hi, hj] at native
    exact (coefficient native).elim

variable {A T : Type*} [Fintype A]

def familyInteraction (shifts : A → M → M)
    (kernels : A → M → I → I → Module.End ℂ B) : Module.End ℂ (Wave M I B N) :=
  ∑ a : A, interaction (shifts a) (kernels a)

theorem family_raises_occupation (target : Finset I) (shifts : A → M → M)
    (kernels : A → M → I → I → Module.End ℂ B)
    (source_support : ∀ a p i j, kernels a p i j ≠ 0 → i ∈ target ∧ j ∉ target) :
    SourceWavepacketGrade.grade (occupation target) * familyInteraction (N := N) shifts kernels =
      familyInteraction shifts kernels * SourceWavepacketGrade.grade (occupation target) +
        familyInteraction shifts kernels := by
  simp only [familyInteraction, Finset.mul_sum, Finset.sum_mul,
    interaction_raises_occupation target _ _ (source_support _), Finset.sum_add_distrib]

theorem time_ordered_family_word_zero (target : Finset I)
    (shifts : T → A → M → M) (kernels : T → A → M → I → I → Module.End ℂ B)
    (source_support : ∀ t a p i j, kernels t a p i j ≠ 0 → i ∈ target ∧ j ∉ target)
    (times : List T) (long_word : N < times.length) :
    (times.map (fun t => familyInteraction (N := N) (shifts t) (kernels t))).prod = 0 := by
  apply SourceWavepacketGrade.bounded_grade_word_zero (occupation target) N
    (occupation_bound target) _ _ (by simpa using long_word)
  intro U member
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp member
  exact family_raises_occupation target (shifts t) (kernels t) (source_support t)

omit [DecidableEq I] in
theorem family_preserves_alternating (shifts : A → M → M)
    (kernels : A → M → I → I → Module.End ℂ B) (ψ : Wave M I B N)
    (fermionic : Alternating ψ) : Alternating (familyInteraction shifts kernels ψ) := by
  intro e
  simp only [familyInteraction, LinearMap.sum_apply, map_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact interaction_preserves_alternating (shifts a) (kernels a) ψ fermionic e

end
end SourceWavepacketInteraction
