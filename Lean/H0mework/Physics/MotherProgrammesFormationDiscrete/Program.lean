import H0mework.Physics.MotherProgrammesFormation.FamilyOccurrenceConsumer
import Mathlib.Logic.Encodable.Basic

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.StageEightDiscreteFormation

open StageNineEnrichedProofFreeSource SU7RicherLineageResponsibility SU7A6GaugeStableRootGraphAdapter
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StandardModelConstraint

noncomputable section

/-- Twelve independent integer slots retain the whole A6 root and both
three-node potentials. The path remains the original multiset of stable roots. -/
abbrev IntegerSlot := (Fin 6) ⊕ P506SourceAffineL0PhaseNode
abbrev Material := (IntegerSlot → ℤ) × SourcePathData × ℕ × ℕ

/-- Signed integer units, one original stable-root move, and two natural units. -/
abbrev Instruction := (Bool × IntegerSlot) ⊕ ((Fin 3) ⊕ Bool)

def integerAtom (slot : IntegerSlot) (value : ℤ) : Material := ⟨Pi.single slot value, 0, 0, 0⟩

def atom : Instruction → Material
  | .inl (true, slot) => integerAtom slot 1
  | .inl (false, slot) => integerAtom slot (-1)
  | .inr (.inl root) => ⟨0, {root}, 0, 0⟩
  | .inr (.inr false) => ⟨0, 0, 1, 0⟩
  | .inr (.inr true) => ⟨0, 0, 0, 1⟩

def advance (instruction : Instruction) (material : Material) : Material := material + atom instruction

def run : List Instruction → Material
  | [] => 0
  | instruction :: rest => atom instruction + run rest

def execute (program : List Instruction) (material : Material) : Material := material + run program

theorem execute_cons (instruction : Instruction) (rest : List Instruction) (material : Material) :
    execute (instruction :: rest) material = execute rest (advance instruction material) :=
  (add_assoc _ _ _).symm

theorem run_append (first second : List Instruction) : run (first ++ second) = run first + run second := by
  induction first with
  | nil => simp [run]
  | cons instruction rest induction => simp only [List.cons_append, run, induction, add_assoc]

theorem run_next (program : List Instruction) (instruction : Instruction) :
    run (program ++ [instruction]) = advance instruction (run program) := by
  rw [run_append]
  simp [run, advance]

def movesWord : List Instruction → List (Fin 3)
  | [] => []
  | .inr (.inl root) :: rest => root :: movesWord rest
  | _ :: rest => movesWord rest

theorem movesWord_readback (program : List Instruction) :
    (movesWord program : SourcePathData) = (run program).2.1 := by
  induction program with
  | nil => rfl
  | cons instruction rest induction =>
      rcases instruction with ⟨sign, slot⟩ | (root | flag)
      · cases sign <;> simpa [movesWord, run, atom, integerAtom] using induction
      · simpa [movesWord, run, atom] using congrArg (Multiset.cons root) induction
      · cases flag <;> simpa [movesWord, run, atom] using induction

def toSource (material : Material) : SmoothUnifiedSource :=
  { Runtime.source with stageEight :=
    { Runtime.source.stageEight with
      sourceRoot := fun coordinate => material.1 (.inl coordinate)
      sourceMoves := material.2.1
      p506PhasePotential := fun node => material.1 (.inr node)
      sigmaSeed := material.2.2.1
      colorScale := material.2.2.2 } }

def readMaterial (source : SmoothUnifiedSource) : Material :=
  ⟨Sum.elim source.stageEight.sourceRoot source.stageEight.p506PhasePotential,
    source.stageEight.sourceMoves, source.stageEight.sigmaSeed, source.stageEight.colorScale⟩

theorem full_material_recovered (material : Material) : readMaterial (toSource material) = material := by
  rcases material with ⟨integers, moves, sigma, color⟩
  apply Prod.ext
  · funext slot
    cases slot <;> rfl
  · rfl

/-- The neutral construction origin is the internally computed difference
of the mother's own material, including its original color unit. -/
def neutralOrigin : Material :=
  let original := readMaterial Runtime.source
  ⟨original.1-original.1, original.2.1-original.2.1,
    original.2.2.1-original.2.2.1, original.2.2.2-original.2.2.2⟩

theorem neutral_origin_zero : neutralOrigin = 0 := by simp [neutralOrigin]

theorem execute_from_mother (program : List Instruction) : execute program neutralOrigin = run program := by
  rw [execute, neutral_origin_zero, zero_add]

theorem ordered_path_generated (program : List Instruction) :
    su7A6StableRootAction (toSource (run program)).stageEight.sourceRoot (movesWord program) =
      (toSource (run program)).stageEight.generatedP506L0Lineage.sourceLabel := by
  rw [orderedAction_eq_generatedLabel, movesWord_readback]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.StageEightDiscreteFormation
