import H0mework.Physics.MotherProgrammesFormationDiscrete.History

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneratedDiscreteRecurrence

open Stage9C.Revision StageEightDiscreteFormation MotherFamilyOccurrence

noncomputable section

def cancellation : List Instruction := [.inl (true, .inl 0), .inl (false, .inl 0)]

theorem cancellation_run : run cancellation = 0 := by
  apply Prod.ext
  · funext coordinate
    simp [run, cancellation, atom, integerAtom, Pi.single_apply]
    split_ifs <;> norm_num
  · rfl

/-- Each extension retains the entire preceding word and appends two actual
signed unit operations. Only their complete material result cancels. -/
def padded (program : List Instruction) : ℕ → List Instruction
  | 0 => program
  | count+1 => padded program count ++ cancellation

theorem run_padded (program : List Instruction) (count : ℕ) : run (padded program count) = run program := by
  induction count with
  | zero => rfl
  | succ count induction => rw [padded, run_append, cancellation_run, add_zero, induction]

theorem padded_length (program : List Instruction) (count : ℕ) :
    (padded program count).length = program.length + 2*count := by
  induction count with
  | zero => simp [padded]
  | succ count induction =>
      simp only [padded, List.length_append, induction, cancellation, List.length_cons, List.length_nil]
      omega

def paddedCode (program : List Instruction) (count : ℕ) : ℕ := Encodable.encodeList (padded program count)

theorem complete_word_recovered (program : List Instruction) (count : ℕ) :
    programAt (paddedCode program count) = padded program count := by
  rw [programAt, paddedCode, decode_program]
  rfl

theorem paddedCode_injective (program : List Instruction) : Function.Injective (paddedCode program) := by
  intro first last same
  have words := congrArg programAt same
  rw [complete_word_recovered, complete_word_recovered] at words
  have lengths := congrArg List.length words
  rw [padded_length, padded_length] at lengths
  omega

theorem code_after_bound (program : List Instruction) (bound : ℕ) : bound ≤ paddedCode program bound := by
  have paid : (padded program bound).length ≤ paddedCode program bound :=
    Encodable.length_le_encode (padded program bound)
  rw [padded_length] at paid
  omega

theorem actual_visits_injective (program : List Instruction) :
    Function.Injective (fun count => SpinPair.visit (10+paddedCode program count)) := by
  intro first last same
  have depths := congrArg (fun visit : MotherVisit => temporalDepth visit.history) same
  rw [visit_depth, visit_depth] at depths
  exact paddedCode_injective program (Nat.add_left_cancel depths)

/-- Every complete discrete material reappears arbitrarily late on this
one fixed original mother history. No new initial state or emitter is selected. -/
theorem arbitrary_late_material (material : Material) (bound : ℕ) :
    ∃ step, bound ≤ step ∧
      readMaterial (sourceAtVisit (SpinPair.visit (10+step))) = material := by
  obtain ⟨program, generated⟩ := every_material_reachable material
  refine ⟨paddedCode program bound, code_after_bound program bound, ?_⟩
  rw [sourceAtVisit, code_at, full_material_recovered, paddedCode, materialAt_program, run_padded, generated]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneratedDiscreteRecurrence
