import H0mework.Versions.R2.Physics.MotherProgrammesFormationDiscrete.Reachability
import Mathlib.Logic.Equiv.List

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.StageEightDiscreteFormation

noncomputable section

/-- This finite inventory contains only the 29 primitive instructions. -/
def alphabet : List Instruction := Finset.univ.toList

instance instructionEncodable : Encodable Instruction :=
  Encodable.encodableOfList alphabet (by intro instruction; simp [alphabet])

def decode (code : ℕ) : Option (List Instruction) := Encodable.decodeList code

theorem decode_zero : decode 0 = some [] := by rw [decode, Encodable.decodeList]

/-- The decoder peels a natural pair and recursively decodes the smaller
tail. It never looks up a completed source or field. -/
theorem decode_next (code : ℕ) :
    decode (code+1) =
      (· :: ·) <$> Encodable.decode (α := Instruction) code.unpair.1 <*> decode code.unpair.2 :=
  Encodable.decode_list_succ code

theorem decode_program (program : List Instruction) :
    decode (Encodable.encodeList program) = some program := Encodable.decodeList_encodeList_eq_self program

def programAt (code : ℕ) : List Instruction := (decode code).getD []

def materialAt (code : ℕ) : Material := execute (programAt code) neutralOrigin

theorem materialAt_program (program : List Instruction) :
    materialAt (Encodable.encodeList program) = run program := by
  rw [materialAt, programAt, decode_program]
  exact execute_from_mother program

theorem every_material_at_code (material : Material) : ∃ code, materialAt code = material := by
  obtain ⟨program, generated⟩ := every_material_reachable material
  exact ⟨Encodable.encodeList program, (materialAt_program program).trans generated⟩

def executionAt (code depth : ℕ) : Material := execute ((programAt code).take depth) neutralOrigin

theorem execution_complete (code : ℕ) : executionAt code (programAt code).length = materialAt code := by
  simp [executionAt, materialAt]

theorem execution_next (code depth : ℕ) (inside : depth < (programAt code).length) :
    executionAt code (depth+1) = advance ((programAt code)[depth]) (executionAt code depth) := by
  rw [executionAt, List.take_succ_eq_append_getElem inside, execute, run_next]
  exact (add_assoc _ _ _).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.StageEightDiscreteFormation
