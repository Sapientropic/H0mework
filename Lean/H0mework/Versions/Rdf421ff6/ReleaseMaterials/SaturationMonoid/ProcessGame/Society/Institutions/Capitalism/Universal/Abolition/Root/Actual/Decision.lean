import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Preferred.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

abbrev State := Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)

def select (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :=
  Material.Migration.Preferred.compile input (origin input depth count) current.raw (members input depth count) prefixLimit renewalLimit

inductive Cause (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Type
  | migration (issue : Material.Migration.Obstruction input (origin input depth count) current.raw
      (members input depth count) prefixLimit renewalLimit)
  | renewal (word : RawEvent Party Good Port Technology Instrument)
      (issue : Review.Guarded.Issue input (origin input depth count) current.raw (members input depth count) word)

def Cause.focus {current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} :
    Cause input depth count prefixLimit renewalLimit current → Repair.Focus (Party := Party) (Good := Good) (Port := Port)
  | .migration issue => Repair.obstructionFocus input depth count prefixLimit renewalLimit issue
  | .renewal _ issue => Repair.guardedFocus input depth count issue

inductive Operation (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Type
  | migration (plan : Material.Migration.Plan input (origin input depth count) current.raw
      (members input depth count) prefixLimit renewalLimit)
      (produced : select input depth count prefixLimit renewalLimit current = .accepted plan)
  | renewal (word : RawEvent Party Good Port Technology Instrument)
      (original : current.phase = .renewal word)
      (checked : Review.Guarded.Checks input (origin input depth count) current.raw (members input depth count) word)
  | repair (cause : Cause input depth count prefixLimit renewalLimit current)
      (attempt : Repair.AttemptAt input depth count current.raw (cause.focus input depth count prefixLimit renewalLimit) current.remaining)

structure ExactObstruction (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) where
  cause : Cause input depth count prefixLimit renewalLimit current
  exhausted : ∀ request ∈ current.remaining,
    ¬ Repair.Relevant input depth count current.raw (cause.focus input depth count prefixLimit renewalLimit) request

inductive Outcome (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Type
  | action (operation : Operation input depth count prefixLimit renewalLimit current)
  | blocked (obstruction : ExactObstruction input depth count prefixLimit renewalLimit current)

def repair (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (cause : Cause input depth count prefixLimit renewalLimit current) : Outcome input depth count prefixLimit renewalLimit current :=
  match Repair.choose input depth count current.raw (cause.focus input depth count prefixLimit renewalLimit) current.remaining with
  | .attempt attempt => .action (.repair cause attempt)
  | .exhausted noCode => .blocked ⟨cause, noCode⟩

/-- There is no supplied successful plan or target. Every branch is read
from this actual current and the original finite unconsumed source code. -/
def decide (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    Outcome input depth count prefixLimit renewalLimit current :=
  match phase : current.phase with
  | .seeking => match produced : select input depth count prefixLimit renewalLimit current with
    | .accepted plan => .action (.migration plan produced)
    | .obstructed issue => repair input depth count prefixLimit renewalLimit current (.migration issue)
  | .renewal word => match Review.Guarded.inspect input (origin input depth count) current.raw (members input depth count) word with
    | .accepted checked => .action (.renewal word phase checked)
    | .rejected issue => repair input depth count prefixLimit renewalLimit current (.renewal word issue)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual
