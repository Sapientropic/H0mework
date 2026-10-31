import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.JointAuthority

/-!
# Joint continuations retaining original internal consents

Finite group authorization is checked anew at each current; original internal
consents are retained.  This is group closure, not by itself freedom from C.  Failure remains
`none`; it never becomes an empty successful programme.  A successful tail
generates every finite continuation with the same material and financial
states as the actual tail.  The tail theorem is a consumer of the trajectory,
not a completed future installed in the source.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.JointProgramme

open Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (program : RawProgram Party Good Port Technology Instrument) (group : List Party)

def attempt (current : RawCurrent Party Good Technology Instrument) :=
  program.law.jointWord group current (program.emit current)

def next? (current : RawCurrent Party Good Technology Instrument) :
    Option (RawCurrent Party Good Technology Instrument) :=
  (attempt program group current).map (program.law.next current)

def run (initial : RawCurrent Party Good Technology Instrument) :
    Nat → Option (RawCurrent Party Good Technology Instrument)
  | 0 => some initial
  | n + 1 => (run initial n).bind (next? program group)

theorem successful_next (current : RawCurrent Party Good Technology Instrument)
    (independent : RawEvent Party Good Port Technology Instrument)
    (produced : attempt program group current = some independent) :
    next? program group current = some (program.tick current) := by
  unfold next?
  rw [produced, Option.map_some]
  exact congrArg some
    (program.law.jointWord_same_next group current (program.emit current) independent produced)

theorem run_original_tail (start : Nat)
    (successful : ∀ n, attempt program group (program.currentAt (start + n)) ≠ none) :
    ∀ length, run program group (program.currentAt start) length =
      some (program.currentAt (start + length)) := by
  intro length
  induction length with
  | zero => simp only [run, Nat.add_zero]
  | succ length ih =>
      simp only [run, ih, Option.bind_some]
      cases produced : attempt program group (program.currentAt (start + length)) with
      | none => exact False.elim (successful length produced)
      | some independent =>
          have next := successful_next program group _ independent produced
          rw [Nat.add_succ]
          exact next

def SelfExecutableTail (start : Nat) : Prop :=
  (∀ length, run program group (program.currentAt start) length =
    some (program.currentAt (start + length))) ∧
  (∀ offset, ∃ independent,
    attempt program group (program.currentAt (start + offset)) = some independent ∧
    independent.map Request.operation =
      (program.emit (program.currentAt (start + offset))).map Request.operation ∧
    ∀ item ∈ (program.law.execute (program.currentAt (start + offset)) 0 independent).items,
      program.law.Valid item.before item.request ∧
        item.request.signer ∈ group ∧ ∀ person ∈ item.request.consents, person ∈ group)

theorem successful_tail_generated (start : Nat)
    (successful : ∀ n, attempt program group (program.currentAt (start + n)) ≠ none) :
    SelfExecutableTail program group start := by
  refine ⟨run_original_tail program group start successful, ?_⟩
  intro offset
  cases produced : attempt program group (program.currentAt (start + offset)) with
  | none => exact False.elim (successful offset produced)
  | some independent =>
      have sound := program.law.jointWord_sound group
        (program.currentAt (start + offset)) (program.emit (program.currentAt (start + offset)))
        independent produced 0
      exact ⟨independent, rfl, sound.2.2, sound.2.1⟩

/-- The alternatives concern authorization of the actual complete word.
Optional blocked actions are not silently relabelled necessary dependence. -/
theorem recurrent_original_obstruction_or_generated_tail :
    (∀ start, ∃ n ≥ start, ∃ item ∈
      program.law.rawItems (program.currentAt n) (program.emit (program.currentAt n)),
        ¬ program.law.Valid item.before item.request ∨
          ∀ signer ∈ group, ¬ program.law.Valid item.before (item.request.jointlyAuthorize group signer)) ∨
    ∃ start, SelfExecutableTail program group start := by
  classical
  by_cases recurring : ∀ start, ∃ n ≥ start,
      attempt program group (program.currentAt n) = none
  · left
    intro start
    obtain ⟨n, after, blocked⟩ := recurring start
    obtain ⟨item, member, obstruction⟩ := program.law.jointWord_failure_original group
      (program.currentAt n) (program.emit (program.currentAt n)) blocked 0
    exact ⟨n, after, item, member, obstruction⟩
  · right
    push Not at recurring
    obtain ⟨start, successful⟩ := recurring
    exact ⟨start, successful_tail_generated program group start
      (fun offset => successful (start + offset) (by omega))⟩

#print axioms successful_tail_generated
#print axioms recurrent_original_obstruction_or_generated_tail

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.JointProgramme
