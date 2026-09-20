import H0mework.Physics.MotherProgrammesFormationDiscrete.Program
import Mathlib.Algebra.BigOperators.Pi

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.StageEightDiscreteFormation

noncomputable section

def Reachable (material : Material) : Prop := ∃ program, run program = material

theorem reachable_add {first second : Material} (left : Reachable first) (right : Reachable second) :
    Reachable (first + second) := by
  obtain ⟨left, left_eq⟩ := left
  obtain ⟨right, right_eq⟩ := right
  exact ⟨left ++ right, by rw [run_append, left_eq, right_eq]⟩

theorem run_replicate (count : ℕ) (instruction : Instruction) :
    run (List.replicate count instruction) = count • atom instruction := by
  induction count with
  | zero => simp [run]
  | succ count induction => simp [List.replicate_succ, run, induction, succ_nsmul, add_comm]

def integerProgram (slot : IntegerSlot) : ℤ → List Instruction
  | .ofNat count => List.replicate count (.inl (true, slot))
  | .negSucc count => List.replicate (count+1) (.inl (false, slot))

theorem run_integerProgram (slot : IntegerSlot) (value : ℤ) :
    run (integerProgram slot value) = integerAtom slot value := by
  cases value with
  | ofNat count =>
      rw [integerProgram, run_replicate]
      ext coordinate <;> simp [atom, integerAtom, Pi.single_apply, nsmul_eq_mul]
  | negSucc count =>
      rw [integerProgram, run_replicate]
      ext coordinate <;> simp [atom, integerAtom, Pi.single_apply, nsmul_eq_mul, Int.negSucc_eq]

private theorem reachable_sum {I : Type} [DecidableEq I] (indices : Finset I) (material : I → Material)
    (each : ∀ index ∈ indices, Reachable (material index)) : Reachable (∑ index ∈ indices, material index) := by
  revert each
  induction indices using Finset.induction_on with
  | empty => intro _; exact ⟨[], rfl⟩
  | @insert index indices absent induction =>
      intro each
      rw [Finset.sum_insert absent]
      exact reachable_add (each index (Finset.mem_insert_self _ _))
        (induction (fun other member => each other (Finset.mem_insert_of_mem member)))

private theorem integer_sum (values : IntegerSlot → ℤ) :
    (∑ slot : IntegerSlot, integerAtom slot (values slot)) = (values, 0, 0, 0) := by
  have integers : (∑ slot : IntegerSlot, Pi.single slot (values slot)) = values :=
    funext (fun slot => Fintype.sum_pi_single slot values)
  simp only [integerAtom, ← prod_mk_sum, Finset.sum_const_zero, integers]

theorem integer_reachable (values : IntegerSlot → ℤ) : Reachable (values, 0, 0, 0) := by
  rw [← integer_sum values]
  exact reachable_sum Finset.univ _ (fun slot _ => ⟨integerProgram slot (values slot), run_integerProgram _ _⟩)

theorem moves_reachable (moves : Multiset (Fin 3)) : Reachable (0, moves, 0, 0) := by
  induction moves using Multiset.induction_on with
  | empty => exact ⟨[], rfl⟩
  | cons root moves induction =>
      have one : Reachable (0, ({root} : Multiset (Fin 3)), 0, 0) :=
        ⟨[.inr (.inl root)], by simp [run, atom]⟩
      simpa using reachable_add one induction

theorem sigma_reachable (count : ℕ) : Reachable (0, 0, count, 0) :=
  ⟨List.replicate count (.inr (.inr false)), by rw [run_replicate]; simp [atom]⟩

theorem color_reachable (count : ℕ) : Reachable (0, 0, 0, count) :=
  ⟨List.replicate count (.inr (.inr true)), by rw [run_replicate]; simp [atom]⟩

/-- Every complete discrete target has a finite unit program. The proof
builds words from integer signs, root moves and natural units, not a Source witness. -/
theorem every_material_reachable (material : Material) : Reachable material := by
  rcases material with ⟨values, moves, sigma, color⟩
  simpa using reachable_add (reachable_add (reachable_add (integer_reachable values)
    (moves_reachable moves)) (sigma_reachable sigma)) (color_reachable color)

theorem every_material_from_mother (material : Material) :
    ∃ program, execute program neutralOrigin = material := by
  obtain ⟨program, generated⟩ := every_material_reachable material
  exact ⟨program, (execute_from_mother program).trans generated⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.StageEightDiscreteFormation
