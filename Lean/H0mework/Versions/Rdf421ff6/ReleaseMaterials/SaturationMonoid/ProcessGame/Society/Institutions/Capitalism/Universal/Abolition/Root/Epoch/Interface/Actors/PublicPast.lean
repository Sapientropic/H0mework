import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Location
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.ActualOccurrence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicPast

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root


noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Registered.Compile.RawInput Party Good Port Technology Instrument))

abbrev Input := Registered.Compile.RawInput Party Good Port Technology Instrument

def eventTag (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Tag input depth count :=
  .publicActual prefixLimit renewalLimit oldPast (ActualOccurrence.eventCursor past raw)

def eventVisit (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :=
  (root input depth count (eventTag input depth count prefixLimit renewalLimit oldPast past raw)).initialVisit

def atEvent (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (party : Party) :
    Option (Location input depth count) :=
  if present : presentAt input depth count (eventTag input depth count prefixLimit renewalLimit oldPast past raw)
      (eventVisit input depth count prefixLimit renewalLimit oldPast past raw) party then
    some (.epoch (eventTag input depth count prefixLimit renewalLimit oldPast past raw)
      (eventVisit input depth count prefixLimit renewalLimit oldPast past raw) party present)
  else none

theorem atEvent_key (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (party : Party) (location : Location input depth count)
    (found : atEvent input depth count prefixLimit renewalLimit oldPast past raw party = some location) :
    location.party input depth count = party := by
  unfold atEvent at found
  split at found
  · cases Option.some.inj found; rfl
  · cases found

/-- The result is the first existing M0 location in the finite input past.
No raw party key is promoted to an actor, and incoming code is not scanned. -/
def scan (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) :
    List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) → Party → Option (Location input depth count)
  | [], _ => none
  | raw :: remaining, party => (atEvent input depth count prefixLimit renewalLimit oldPast past raw party).orElse
      (fun _ => scan (past ++ [raw]) remaining party)

def first (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (party : Party) := scan input depth count prefixLimit renewalLimit oldPast [] past party

theorem scan_key (past remaining : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (party : Party) (location : Location input depth count)
    (found : scan input depth count prefixLimit renewalLimit oldPast past remaining party = some location) :
    location.party input depth count = party := by
  induction remaining generalizing past with
  | nil => cases found
  | cons raw remaining inherited =>
      change (atEvent input depth count prefixLimit renewalLimit oldPast past raw party).orElse _ = _ at found
      cases occurred : atEvent input depth count prefixLimit renewalLimit oldPast past raw party with
      | some original =>
          simp only [occurred, Option.orElse_some, Option.some.injEq] at found
          subst location
          exact atEvent_key input depth count prefixLimit renewalLimit oldPast past raw party original occurred
      | none =>
          simp only [occurred, Option.orElse_none] at found
          exact inherited _ found

theorem first_key (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (party : Party) (location : Location input depth count)
    (found : first input depth count prefixLimit renewalLimit oldPast past party = some location) :
    location.party input depth count = party := scan_key input depth count prefixLimit renewalLimit oldPast [] past party location found

theorem scan_append (past left right : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (party : Party) :
    scan input depth count prefixLimit renewalLimit oldPast past (left ++ right) party =
      (scan input depth count prefixLimit renewalLimit oldPast past left party).orElse
        (fun _ => scan input depth count prefixLimit renewalLimit oldPast (past ++ left) right party) := by
  induction left generalizing past with
  | nil => simp only [List.nil_append, scan, Option.orElse_none, List.append_nil]
  | cons raw remaining inherited =>
      simp only [List.cons_append, scan, inherited, List.append_assoc]
      cases atEvent input depth count prefixLimit renewalLimit oldPast past raw party <;> rfl

theorem first_append (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (party : Party) :
    first input depth count prefixLimit renewalLimit oldPast (past ++ [raw]) party =
      (first input depth count prefixLimit renewalLimit oldPast past party).orElse
        (fun _ => atEvent input depth count prefixLimit renewalLimit oldPast past raw party) := by
  unfold first
  rw [scan_append]
  simp only [List.nil_append, scan]
  cases scan input depth count prefixLimit renewalLimit oldPast [] past party <;>
    cases atEvent input depth count prefixLimit renewalLimit oldPast past raw party <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicPast
