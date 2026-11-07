import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Source
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Prefix

/-! The start cursor chooses a local root entry, not another physical event.
The complete current cursor retains the input past and fixes a shared
occurrence view. No successor is executed by this restriction. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.ActualOccurrence

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

abbrev RawInput := Registered.Compile.RawInput Party Good Port Technology Instrument

def eventCursor (past : List (RawInput (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : RawInput (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :=
  Registered.Physical.receive (Registered.Physical.Prefix.cursor past) raw

def eventTag (prefixLimit renewalLimit : Nat)
    (past : List (RawInput (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : RawInput (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Tag input depth count :=
  .actual prefixLimit renewalLimit (eventCursor past raw)

def eventVisit (prefixLimit renewalLimit : Nat)
    (past : List (RawInput (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : RawInput (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :=
  (root input depth count (eventTag input depth count prefixLimit renewalLimit past raw)).initialVisit

def tagOf : (tag : Tag input depth count) → Visit input depth count tag → Tag input depth count
  | .review datum limit, _ => .review datum limit
  | .migration prefixLimit renewalLimit, _ => .migration prefixLimit renewalLimit
  | .actual prefixLimit renewalLimit _, visit => .actual prefixLimit renewalLimit visit.current
  | .publicActual prefixLimit renewalLimit oldPast _, visit => .publicActual prefixLimit renewalLimit oldPast visit.current

def visitOf : (tag : Tag input depth count) → (visit : Visit input depth count tag) →
    Visit input depth count (tagOf input depth count tag visit)
  | .review _ _, visit => visit
  | .migration _ _, visit => visit
  | .actual prefixLimit renewalLimit _, visit =>
      (root input depth count (.actual prefixLimit renewalLimit visit.current)).initialVisit
  | .publicActual prefixLimit renewalLimit oldPast _, visit =>
      (root input depth count (.publicActual prefixLimit renewalLimit oldPast visit.current)).initialVisit

theorem same_interpreter (tag : Tag input depth count) (visit : Visit input depth count tag) :
    interpreter input depth count (tagOf input depth count tag visit) = interpreter input depth count tag := by cases tag <;> rfl

theorem same_body (tag : Tag input depth count) (visit : Visit input depth count tag) :
    body input depth count (tagOf input depth count tag visit) (visitOf input depth count tag visit) =
      body input depth count tag visit := by cases tag <;> rfl

theorem same_execution (tag : Tag input depth count) (visit : Visit input depth count tag) :
    execution input depth count (tagOf input depth count tag visit) (visitOf input depth count tag visit).current =
      execution input depth count tag visit.current := by cases tag <;> rfl

theorem same_actual_emission (tag : Tag input depth count) (visit : Visit input depth count tag) :
    HEq ((root input depth count (tagOf input depth count tag visit)).emitted (visitOf input depth count tag visit).current)
      ((root input depth count tag).emitted visit.current) := by cases tag <;> rfl

theorem same_original_row (tag : Tag input depth count) (visit : Visit input depth count tag) :
    HEq (entry input depth count (tagOf input depth count tag visit) (visitOf input depth count tag visit))
      (entry input depth count tag visit) := by cases tag <;> rfl

theorem same_compiled_next (tag : Tag input depth count) (visit : Visit input depth count tag) :
    HEq (((root input depth count (tagOf input depth count tag visit)).evolutionAt
      (visitOf input depth count tag visit).current).nextCurrent?)
      (((root input depth count tag).evolutionAt visit.current).nextCurrent?) := by cases tag <;> rfl

theorem actual_source_next_at (prefixLimit renewalLimit : Nat)
    (start : Registered.Physical.Cursor Party Good Port Technology Instrument)
    (visit : Visit input depth count (.actual prefixLimit renewalLimit start)) :
    ((root input depth count (.actual prefixLimit renewalLimit start)).evolutionAt visit.current).nextCurrent? =
      some (Registered.Physical.next visit.current) := by
  let current : Registered.Physical.Cursor Party Good Port Technology Instrument := visit.current
  have compiled := Registered.Physical.compiler_eq_source_choice input depth count prefixLimit renewalLimit start current
  have next := congrArg (fun value : EvolutionAt (Registered.Physical.V input depth count prefixLimit renewalLimit) current =>
    value.nextCurrent?) compiled
  split at next <;> exact next

def item : ActualItem input depth count → ActualItem input depth count
  | ⟨.review datum limit, visit, position⟩ => ⟨.review datum limit, visit, position⟩
  | ⟨.migration prefixLimit renewalLimit, visit, position⟩ => ⟨.migration prefixLimit renewalLimit, visit, position⟩
  | ⟨.actual prefixLimit renewalLimit _, visit, position⟩ =>
      ⟨.actual prefixLimit renewalLimit visit.current,
        (root input depth count (.actual prefixLimit renewalLimit visit.current)).initialVisit, position⟩
  | ⟨.publicActual prefixLimit renewalLimit oldPast _, visit, position⟩ =>
      ⟨.publicActual prefixLimit renewalLimit oldPast visit.current,
        (root input depth count (.publicActual prefixLimit renewalLimit oldPast visit.current)).initialVisit, position⟩

theorem item_instruction (original : ActualItem input depth count) :
    (item input depth count original).instruction input depth count = original.instruction input depth count := by
  rcases original with ⟨tag, visit, position⟩
  cases tag <;> rfl

theorem item_position (original : ActualItem input depth count) :
    (item input depth count original).position.val = original.position.val := by
  rcases original with ⟨tag, visit, position⟩
  cases tag <;> rfl

theorem item_idempotent (original : ActualItem input depth count) :
    item input depth count (item input depth count original) = item input depth count original := by
  rcases original with ⟨tag, visit, position⟩
  cases tag <;> rfl

theorem distinct_pasts_are_not_merged (prefixLimit renewalLimit : Nat)
    (firstStart secondStart : Registered.Physical.Cursor Party Good Port Technology Instrument)
    (first : Visit input depth count (.actual prefixLimit renewalLimit firstStart))
    (second : Visit input depth count (.actual prefixLimit renewalLimit secondStart))
    (firstPosition : Fin (execution input depth count (.actual prefixLimit renewalLimit firstStart) first.current).items.length)
    (secondPosition : Fin (execution input depth count (.actual prefixLimit renewalLimit secondStart) second.current).items.length)
    (different : first.current.past ≠ second.current.past) :
    item input depth count ⟨.actual prefixLimit renewalLimit firstStart, first, firstPosition⟩ ≠
      item input depth count ⟨.actual prefixLimit renewalLimit secondStart, second, secondPosition⟩ := by
  intro same
  have tags := congrArg ActualItem.tag same
  have currents := (Tag.actual.inj tags).2.2
  exact different (congrArg Registered.Physical.Cursor.past currents)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem reconstruction_has_the_same_cursor
    (current : Registered.Physical.Cursor Party Good Port Technology Instrument) :
    eventCursor current.past current.incoming = current := Registered.Physical.Prefix.reconstructs_the_same_cursor current

#print axioms same_actual_emission
#print axioms same_original_row
#print axioms same_compiled_next
#print axioms item_instruction

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.ActualOccurrence
