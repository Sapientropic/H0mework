import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Census

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.CurrentScope

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)

def rawAt := (Physical.stateAt input depth count prefixLimit renewalLimit current.past).raw

/-- The existing M0 census is read directly from this consumed physical
prefix. The following word adds incidences to be checked, not new actors. -/
def scope (word : RawEvent Party Good Port Technology Instrument) : List Party :=
  (Epoch.Interface.Actors.Census.parties input depth count prefixLimit renewalLimit current ++
    Source.ProgrammeFace.parties input.law (rawAt input depth count prefixLimit renewalLimit current, word)).dedup

abbrev Checks (word : RawEvent Party Good Port Technology Instrument) :=
  Review.Guarded.Checks input (Actual.origin input depth count)
    (rawAt input depth count prefixLimit renewalLimit current)
    (scope input depth count prefixLimit renewalLimit current word) word

structure Failure where
  word : RawEvent Party Good Port Technology Instrument
  phase : (Physical.stateAt input depth count prefixLimit renewalLimit current.past).phase = .renewal word
  issue : Review.Guarded.Issue input (Actual.origin input depth count)
    (rawAt input depth count prefixLimit renewalLimit current)
    (scope input depth count prefixLimit renewalLimit current word) word

theorem Failure.refutes (failure : Failure input depth count prefixLimit renewalLimit current) :
    ¬ Checks input depth count prefixLimit renewalLimit current failure.word :=
  failure.issue.refutes input _ _ _ _

inductive View : Type
  | seeking (phase : (Physical.stateAt input depth count prefixLimit renewalLimit current.past).phase = .seeking)
  | accepted (word : RawEvent Party Good Port Technology Instrument)
      (phase : (Physical.stateAt input depth count prefixLimit renewalLimit current.past).phase = .renewal word)
      (checked : Checks input depth count prefixLimit renewalLimit current word)
  | rejected (failure : Failure input depth count prefixLimit renewalLimit current)

/-- This is a source-only current test. It accepts no successful successor,
actor inventory, query or future policy as an argument. -/
def inspect : View input depth count prefixLimit renewalLimit current :=
  match phase : (Physical.stateAt input depth count prefixLimit renewalLimit current.past).phase with
  | .seeking => .seeking phase
  | .renewal word =>
      match Review.Guarded.inspect input (Actual.origin input depth count)
          (rawAt input depth count prefixLimit renewalLimit current)
          (scope input depth count prefixLimit renewalLimit current word) word with
      | .accepted checked => .accepted word phase checked
      | .rejected issue => .rejected ⟨word, phase, issue⟩

def failure? : Option (Failure input depth count prefixLimit renewalLimit current) :=
  match inspect input depth count prefixLimit renewalLimit current with
  | .rejected failure => some failure
  | _ => none

abbrev Clear : Prop := (failure? input depth count prefixLimit renewalLimit current).isNone = true

theorem clear_iff_no_failure : Clear input depth count prefixLimit renewalLimit current ↔
    failure? input depth count prefixLimit renewalLimit current = none := by
  unfold Clear
  cases failure? input depth count prefixLimit renewalLimit current <;> simp

theorem a_checked_current_has_no_scope_failure
    (word : RawEvent Party Good Port Technology Instrument)
    (phase : (Physical.stateAt input depth count prefixLimit renewalLimit current.past).phase = .renewal word)
    (whole : Checks input depth count prefixLimit renewalLimit current word) :
    Clear input depth count prefixLimit renewalLimit current := by
  cases inspected : inspect input depth count prefixLimit renewalLimit current with
  | accepted target targetPhase checked => simp only [Clear, failure?, inspected, Option.isNone_none]
  | seeking no => exact False.elim (by cases no.symm.trans phase)
  | rejected failure =>
      have same : failure.word = word := Actual.Phase.renewal.inj (failure.phase.symm.trans phase)
      exact (failure.refutes input depth count prefixLimit renewalLimit current (same.symm ▸ whole)).elim

theorem a_seeking_current_has_no_scope_failure
    (phase : (Physical.stateAt input depth count prefixLimit renewalLimit current.past).phase = .seeking) :
    Clear input depth count prefixLimit renewalLimit current := by
  cases inspected : inspect input depth count prefixLimit renewalLimit current with
  | seeking no => simp only [Clear, failure?, inspected, Option.isNone_none]
  | accepted word selected checked => exact False.elim (by cases phase.symm.trans selected)
  | rejected failure => exact False.elim (by cases phase.symm.trans failure.phase)

def automaticRenewal : Bool :=
  match Actual.decide input depth count prefixLimit renewalLimit
      (Physical.stateAt input depth count prefixLimit renewalLimit current.past) with
  | .action (.renewal ..) => true
  | _ => false

/-- A failed old word does not forbid a native repair or a new migration.
The actual hazard is an old compiler approving that word as a renewal. -/
def hazard? : Option (Failure input depth count prefixLimit renewalLimit current) :=
  match failure? input depth count prefixLimit renewalLimit current with
  | none => none
  | some failure =>
      if automaticRenewal input depth count prefixLimit renewalLimit current then some failure else none

abbrev Safe : Prop := (hazard? input depth count prefixLimit renewalLimit current).isNone = true

theorem safe_iff_no_hazard : Safe input depth count prefixLimit renewalLimit current ↔
    hazard? input depth count prefixLimit renewalLimit current = none := by
  unfold Safe
  cases hazard? input depth count prefixLimit renewalLimit current <;> simp

theorem a_clear_scope_has_no_renewal_hazard
    (clear : Clear input depth count prefixLimit renewalLimit current) :
    Safe input depth count prefixLimit renewalLimit current := by
  have cleared := (clear_iff_no_failure input depth count prefixLimit renewalLimit current).mp clear
  simp only [Safe, hazard?, cleared, Option.isNone_none]

theorem an_actual_repair_or_migration_keeps_its_source_route
    (different : automaticRenewal input depth count prefixLimit renewalLimit current = false) :
    Safe input depth count prefixLimit renewalLimit current := by
  unfold Safe hazard?
  cases failure? input depth count prefixLimit renewalLimit current <;> simp only [different, Bool.false_eq_true, if_false, Option.isNone_none]

theorem every_original_member_is_in_the_actual_scope
    (word : RawEvent Party Good Port Technology Instrument) (person : Party)
    (present : person ∈ Actual.members input depth count) :
    person ∈ scope input depth count prefixLimit renewalLimit current word :=
  List.mem_dedup.mpr (List.mem_append_left _
    (List.mem_dedup.mpr (List.mem_append_left _ present)))

theorem accepted_checks_restrict_to_the_original_compiler
    (word : RawEvent Party Good Port Technology Instrument)
    (whole : Checks input depth count prefixLimit renewalLimit current word) :
    Review.Guarded.Checks input (Actual.origin input depth count)
      (rawAt input depth count prefixLimit renewalLimit current) (Actual.members input depth count) word := by
  have contained := every_original_member_is_in_the_actual_scope input depth count prefixLimit renewalLimit current word
  refine ⟨whole.1, ?_, whole.2.2.1, ?_, whole.2.2.2.2.1, ?_, whole.2.2.2.2.2.2⟩
  · intro cell listed
    obtain ⟨person, member, original⟩ := List.mem_flatMap.mp listed
    exact whole.2.1 cell (List.mem_flatMap.mpr ⟨person, contained person member, original⟩)
  · exact fun person member => whole.2.2.2.1 person (contained person member)
  · exact fun person member => whole.2.2.2.2.2.1 person (contained person member)

#print axioms inspect
#print axioms Failure.refutes
#print axioms accepted_checks_restrict_to_the_original_compiler

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.CurrentScope
