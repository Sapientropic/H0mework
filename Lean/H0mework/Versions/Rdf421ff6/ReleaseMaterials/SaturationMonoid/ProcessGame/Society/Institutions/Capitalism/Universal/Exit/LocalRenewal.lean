import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Necessity

/-! Local needs and authorization generate executable finite continuations.
The membership readout and emitted word may change at each actual current;
no future programme, future success table, or fixed population is stored. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.LocalRenewal

open Source.Program

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (program : RawProgram Party Good Port Technology Instrument)
  (members : RawCurrent Party Good Technology Instrument → List Party)

def attempt (current : RawCurrent Party Good Technology Instrument) :
    Option (RawEvent Party Good Port Technology Instrument) :=
  if Necessity.AllNeedsPaid program.law current (members current) (program.emit current) then
    program.law.jointWord (members current) current (program.emit current)
  else none

def next? (current : RawCurrent Party Good Technology Instrument) :
    Option (RawCurrent Party Good Technology Instrument) :=
  (attempt program members current).map (program.law.next current)

def run (current : RawCurrent Party Good Technology Instrument) :
    Nat → Option (RawCurrent Party Good Technology Instrument)
  | 0 => some current
  | count + 1 => (run current count).bind (next? program members)

theorem attempt_sound (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (generated : attempt program members current = some word) :
    program.law.next current word = program.tick current ∧
    Necessity.AllNeedsPaid program.law current (members current) word ∧
    (∀ item ∈ program.law.rawItems current word,
      program.law.Valid item.before item.request ∧ item.request.signer ∈ members current ∧
        ∀ person ∈ item.request.consents, person ∈ members current) ∧
    word.map Request.operation = (program.emit current).map Request.operation := by
  unfold attempt at generated
  split at generated
  next paid =>
    have sound := program.law.jointWord_sound (members current) current (program.emit current) word generated 0
    exact ⟨program.law.jointWord_same_next (members current) current _ word generated,
      Necessity.allNeedsPaid_jointWord program.law current (members current) _ word generated paid,
      sound.2.1, sound.2.2⟩
  next missing => cases generated

theorem failure_has_original_bearer (current : RawCurrent Party Good Technology Instrument)
    (failed : attempt program members current = none) :
    (∃ person ∈ members current,
      ¬ Necessity.BundlePaid program.law current (program.emit current) person
        (program.law.necessities current person) .necessity ∨
      ¬ Necessity.BundlePaid program.law current (program.emit current) person
        (program.law.mandatoryMaintenance current person) .maintenance) ∨
    (∃ item ∈ program.law.rawItems current (program.emit current),
      ¬ program.law.Valid item.before item.request ∨
        ∀ signer ∈ members current,
          ¬ program.law.Valid item.before (item.request.jointlyAuthorize (members current) signer)) := by
  classical
  by_cases paid : Necessity.AllNeedsPaid program.law current (members current) (program.emit current)
  · right
    simp only [attempt, if_pos paid] at failed
    exact program.law.jointWord_failure_original (members current) current (program.emit current) failed 0
  · left
    unfold Necessity.AllNeedsPaid at paid
    push Not at paid
    obtain ⟨person, member, unpaid⟩ := paid
    refine ⟨person, member, ?_⟩
    by_cases needs : Necessity.BundlePaid program.law current (program.emit current) person
        (program.law.necessities current person) .necessity
    · exact Or.inr (unpaid needs)
    · exact Or.inl needs

theorem successful_next (current : RawCurrent Party Good Technology Instrument)
    (success : attempt program members current ≠ none) :
    next? program members current = some (program.tick current) := by
  cases generated : attempt program members current with
  | none => exact False.elim (success generated)
  | some word =>
      simp only [next?, generated, Option.map_some, (attempt_sound program members current word generated).1]

theorem run_original_tail (start : Nat)
    (available : ∀ n, attempt program members (program.currentAt (start + n)) ≠ none) :
    ∀ length, run program members (program.currentAt start) length =
      some (program.currentAt (start + length)) := by
  intro length
  induction length with
  | zero => simp only [run, Nat.add_zero]
  | succ length ih =>
      simp only [run, ih, Option.bind_some]
      exact successful_next program members _ (available length)

def PaidTail (start : Nat) : Prop :=
  (∀ length, run program members (program.currentAt start) length =
    some (program.currentAt (start + length))) ∧
  (∀ offset, ∃ word,
    attempt program members (program.currentAt (start + offset)) = some word ∧
    Necessity.AllNeedsPaid program.law (program.currentAt (start + offset))
      (members (program.currentAt (start + offset))) word ∧
    (∀ item ∈ program.law.rawItems (program.currentAt (start + offset)) word,
      program.law.Valid item.before item.request ∧
        item.request.signer ∈ members (program.currentAt (start + offset)) ∧
        ∀ person ∈ item.request.consents, person ∈ members (program.currentAt (start + offset))))

theorem successful_tail_generated (start : Nat)
    (available : ∀ n, attempt program members (program.currentAt (start + n)) ≠ none) :
    PaidTail program members start := by
  refine ⟨run_original_tail program members start available, ?_⟩
  intro offset
  cases generated : attempt program members (program.currentAt (start + offset)) with
  | none => exact False.elim (available offset generated)
  | some word =>
      have sound := attempt_sound program members _ word generated
      exact ⟨word, rfl, sound.2.1, sound.2.2.1⟩

/-- Only local source invariance and a finite check at the current enter.
Every future finite continuation is generated by recursion from those laws. -/
theorem local_source_generates_paid_continuation
    (invariant : RawCurrent Party Good Technology Instrument → Prop)
    (initial : invariant program.initial)
    (preserved : ∀ current, invariant current → invariant (program.tick current))
    (available : ∀ current, invariant current → attempt program members current ≠ none) :
    ∀ start, PaidTail program members start := by
  have reached : ∀ n, invariant (program.currentAt n) := by
    intro n
    induction n with
    | zero => exact initial
    | succ n ih => exact preserved _ ih
  intro start
  exact successful_tail_generated program members start (fun n => available _ (reached (start + n)))

#print axioms attempt_sound
#print axioms local_source_generates_paid_continuation

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.LocalRenewal
