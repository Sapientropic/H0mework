import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile.Effect

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

abbrev Input := Compile.RawInput Party Good Port Technology Instrument

/-- The finite past is source code already consumed. Physical state is its
fold from the original frame; no new input may provide a replacement state. -/
structure Cursor (Party Good Port Technology Instrument : Type) where
  private mk ::
  past : List (Compile.RawInput Party Good Port Technology Instrument)
  incoming : Compile.RawInput Party Good Port Technology Instrument

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

def stateAt (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) :=
  past.foldl (Compile.next input depth count prefixLimit renewalLimit) (Actual.initial input depth count)

def initial : Cursor Party Good Port Technology Instrument := ⟨[], .advance⟩

def next (current : Cursor Party Good Port Technology Instrument) : Cursor Party Good Port Technology Instrument :=
  ⟨current.past ++ [current.incoming], .advance⟩

def receive (current : Cursor Party Good Port Technology Instrument)
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    Cursor Party Good Port Technology Instrument := ⟨current.past, raw⟩

theorem consumed_input_generates_its_own_after (current : Cursor Party Good Port Technology Instrument) :
    stateAt input depth count prefixLimit renewalLimit (next current).past =
      Compile.next input depth count prefixLimit renewalLimit
        (stateAt input depth count prefixLimit renewalLimit current.past) current.incoming := by
  simp only [stateAt, next, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem receiving_input_preserves_the_entire_past (current : Cursor Party Good Port Technology Instrument)
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    (receive current raw).past = current.past ∧
    stateAt input depth count prefixLimit renewalLimit (receive current raw).past =
      stateAt input depth count prefixLimit renewalLimit current.past := ⟨rfl, rfl⟩

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem every_old_input_is_retained (current : Cursor Party Good Port Technology Instrument) :
    current.past <+: (next current).past := List.prefix_append _ _

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem next_records_one_actual_attempt (current : Cursor Party Good Port Technology Instrument) :
    (next current).past.length = current.past.length + 1 := by simp [next]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical
