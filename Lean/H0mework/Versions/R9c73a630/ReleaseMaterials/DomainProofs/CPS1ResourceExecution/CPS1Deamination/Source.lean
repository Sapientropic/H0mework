import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.Chemistry
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ResourceExecution.Reactions
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Producer.Target

/-!
The original CPS1 guide addresses generate A-to-I deamination reactions on one whole DNA word.
The minus strand is stored in increasing plus-genomic coordinates, not reversed into 5'-to-3' order.
Opposite-strand recognition reads inosine as G and then C; it does not execute DNA repair.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1Deamination.Source

open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
open CPS1ResourceExecution

/-- Both restrictions retain the original genomic-coordinate order and full word. -/
def originalMinusAligned : List Base := Target.original.map Base.ofOpposite

def plusReadout (word : List Base) : Bases := word.map Base.oppositeRead

/-- Left/right are restrictions of the current word, not a supplied repaired endpoint. -/
structure Step where
  address : Nat
  left : List Base
  right : List Base
  deriving DecidableEq, Repr

def Step.input (step : Step) : List Base := step.left ++ .A :: step.right
def Step.output (step : Step) : List Base := step.left ++ .I :: step.right
def Step.reaction (step : Step) : Reaction := .deaminate step.left step.right

inductive Compilation
  | complete (word : List Base) (steps : List Step)
  | cut (word : List Base) (address : Nat) (pendingTail : List Nat) (steps : List Step)
  deriving DecidableEq, Repr

def Compilation.word : Compilation → List Base
  | .complete word _ | .cut word _ _ _ => word

def Compilation.steps : Compilation → List Step
  | .complete _ steps | .cut _ _ _ steps => steps

def Compilation.pending : Compilation → List Nat
  | .complete _ _ => []
  | .cut _ address pendingTail _ => address :: pendingTail

def Compilation.reactions (result : Compilation) : List Reaction := result.steps.map Step.reaction

def prependStep (step : Step) : Compilation → Compilation
  | .complete word steps => .complete word (step :: steps)
  | .cut word address pendingTail steps => .cut word address pendingTail (step :: steps)

/-- The first non-A or absent address cuts; previous reactions and the current word survive. -/
def compile (initial : List Base) (addresses : List Nat) : Compilation :=
  List.rec (motive := fun _ => List Base → Compilation)
    (fun word => .complete word [])
    (fun address pendingTail next word =>
      match word[address]? with
      | some Base.A =>
          let step : Step := ⟨address, word.take address, word.drop (address + 1)⟩
          prependStep step (next step.output)
      | _ => .cut word address pendingTail []) addresses initial

theorem compile_cons (initial : List Base) (address : Nat) (pendingTail : List Nat) :
    compile initial (address :: pendingTail) =
      match initial[address]? with
      | some Base.A =>
          let step : Step := ⟨address, initial.take address, initial.drop (address + 1)⟩
          prependStep step (compile step.output pendingTail)
      | _ => .cut initial address pendingTail [] := rfl

/-- Flags select one of the already registered eight finite models, never a patient extent. -/
def sourceProgram (edits : Target.Edits) : Compilation :=
  compile originalMinusAligned (Target.positions edits)

def physicalUpdate (edits : Target.Edits) : List Base :=
  (Target.positions edits).foldl (fun word address => word.set address .I) originalMinusAligned

/-- A trace retains every whole intermediate and the exact input of its next reaction. -/
def follows (initial : List Base) (steps : List Step) (final : List Base) : Prop :=
  List.rec (motive := fun _ => List Base → Prop) (fun word => word = final)
    (fun step _ next word => step.input = word ∧ next step.output) steps initial

theorem located_step_input (word : List Base) (address : Nat)
    (located : word[address]? = some .A) :
    (Step.mk address (word.take address) (word.drop (address + 1))).input = word := by
  obtain ⟨inRange, value⟩ := List.getElem?_eq_some_iff.mp located
  unfold Step.input
  rw [← value, List.getElem_cons_drop, List.take_append_drop]

theorem located_step_output (word : List Base) (address : Nat)
    (located : word[address]? = some .A) :
    (Step.mk address (word.take address) (word.drop (address + 1))).output =
      word.set address .I := by
  obtain ⟨inRange, _⟩ := List.getElem?_eq_some_iff.mp located
  simp only [Step.output, List.set_eq_take_append_cons_drop, inRange, if_true]

theorem prepend_follows (step : Step) (result : Compilation)
    (tail : follows step.output result.steps result.word) :
    follows step.input (prependStep step result).steps (prependStep step result).word := by
  cases result <;> exact ⟨rfl, tail⟩

theorem compile_follows (initial : List Base) (addresses : List Nat) :
    follows initial (compile initial addresses).steps (compile initial addresses).word := by
  induction addresses generalizing initial with
  | nil => rfl
  | cons address pendingTail inductionHypothesis =>
      cases located : initial[address]? with
      | none => rw [compile_cons, located]; rfl
      | some base =>
          cases base with
          | A =>
              let step : Step := ⟨address, initial.take address, initial.drop (address + 1)⟩
              rw [compile_cons, located]
              change follows initial (prependStep step (compile step.output pendingTail)).steps
                (prependStep step (compile step.output pendingTail)).word
              have trace := prepend_follows step (compile step.output pendingTail)
                (inductionHypothesis step.output)
              simpa only [step, located_step_input initial address located] using trace
          | C | G | T | I =>
              rw [compile_cons, located]; rfl

theorem compile_address_inventory (initial : List Base) (addresses : List Nat) :
    (compile initial addresses).steps.map Step.address ++
      (compile initial addresses).pending = addresses := by
  induction addresses generalizing initial with
  | nil => rfl
  | cons address pendingTail inductionHypothesis =>
      cases located : initial[address]? with
      | none => simp only [compile_cons, located, Compilation.steps, Compilation.pending,
          List.map_nil, List.nil_append]
      | some base =>
          cases base with
          | A =>
              let step : Step := ⟨address, initial.take address, initial.drop (address + 1)⟩
              rw [compile_cons, located]
              change (prependStep step (compile step.output pendingTail)).steps.map Step.address ++
                (prependStep step (compile step.output pendingTail)).pending = address :: pendingTail
              have inventory := inductionHypothesis step.output
              cases result : compile step.output pendingTail with
              | complete word steps =>
                  simp only [result, Compilation.steps, Compilation.pending] at inventory
                  simpa only [prependStep, Compilation.steps, Compilation.pending, List.map_cons,
                    List.cons_append, List.append_nil, step] using congrArg (address :: ·) inventory
              | cut word invalid rest steps =>
                  simp only [result, Compilation.steps, Compilation.pending] at inventory
                  simpa only [prependStep, Compilation.steps, Compilation.pending, List.map_cons,
                    List.cons_append, step] using congrArg (address :: ·) inventory
          | C | G | T | I =>
              simp only [compile_cons, located, Compilation.steps, Compilation.pending,
                List.map_nil, List.nil_append]

theorem source_whole_word_and_addresses :
    originalMinusAligned.length = 110 ∧
    plusReadout originalMinusAligned = Target.original ∧
    Target.positions ⟨true, true, true⟩ = [70,65,64] ∧
    originalMinusAligned[70]? = some .A ∧
    originalMinusAligned[65]? = some .A ∧
    originalMinusAligned[64]? = some .A := by
  decide +kernel

/-- The complete program is computed from the current A sites; physicalUpdate is a readout. -/
theorem source_program_complete (third eighth ninth : Bool) :
    sourceProgram ⟨third,eighth,ninth⟩ =
      .complete (physicalUpdate ⟨third,eighth,ninth⟩)
        (sourceProgram ⟨third,eighth,ninth⟩).steps := by
  cases third <;> cases eighth <;> cases ninth <;> decide +kernel

theorem source_readout_commutes (third eighth ninth : Bool) :
    plusReadout (sourceProgram ⟨third,eighth,ninth⟩).word =
      Target.genomic ⟨third,eighth,ninth⟩ := by
  cases third <;> cases eighth <;> cases ninth <;> decide +kernel

theorem untouched_update_coordinate (word : List Base) (addresses : List Nat) (coordinate : Nat)
    (untouched : coordinate ∉ addresses) :
    ((addresses.foldl (fun current address => current.set address .I) word))[coordinate]? =
      word[coordinate]? := by
  induction addresses generalizing word with
  | nil => rfl
  | cons address pendingTail inductionHypothesis =>
      have different : address ≠ coordinate := by
        intro equality
        exact untouched (by simp only [List.mem_cons, equality, true_or])
      have tailUntouched : coordinate ∉ pendingTail := by
        intro member
        exact untouched (List.mem_cons_of_mem address member)
      rw [List.foldl_cons, inductionHypothesis (word.set address .I) tailUntouched,
        List.getElem?_set_ne different]

theorem source_untouched_coordinate (third eighth ninth : Bool) (coordinate : Nat)
    (untouched : coordinate ∉ Target.positions ⟨third,eighth,ninth⟩) :
    (sourceProgram ⟨third,eighth,ninth⟩).word[coordinate]? =
      originalMinusAligned[coordinate]? := by
  rw [source_program_complete, Compilation.word]
  exact untouched_update_coordinate originalMinusAligned
    (Target.positions ⟨third,eighth,ninth⟩) coordinate untouched

theorem intended_source_recognition :
    plusReadout (sourceProgram ⟨false,true,false⟩).word =
      SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.genomic ∧
    (sourceProgram ⟨false,true,false⟩).word[65]? = some .I ∧
    (sourceProgram ⟨false,true,false⟩).steps.map Step.address = [65] := by
  decide +kernel

theorem source_three_reactions :
    (sourceProgram ⟨true,true,true⟩).steps.map Step.address = [70,65,64] ∧
    (sourceProgram ⟨true,true,true⟩).reactions.length = 3 ∧
    (sourceProgram ⟨true,true,true⟩).pending = [] := by
  decide +kernel

/-- A repeated site is I in the current intermediate and cuts before a second reaction. -/
theorem repeated_address_control :
    compile [.A] [0,0] = .cut [.I] 0 [] [⟨0,[],[]⟩] ∧
    (compile [.A] [0,0]).reactions.length = 1 := by
  decide +kernel

theorem invalid_address_controls :
    compile [.G] [0,1] = .cut [.G] 0 [1] [] ∧
    compile [.A] [1,0] = .cut [.A] 1 [0] [] ∧
    compile [.A,.C] [0,1,0] = .cut [.I,.C] 1 [0] [⟨0,[],[.C]⟩] := by
  decide +kernel

end CPS1Deamination.Source
