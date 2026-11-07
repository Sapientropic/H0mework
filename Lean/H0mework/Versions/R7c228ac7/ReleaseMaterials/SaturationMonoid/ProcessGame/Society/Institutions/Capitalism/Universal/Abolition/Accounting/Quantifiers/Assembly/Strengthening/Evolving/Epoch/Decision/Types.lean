import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Decision.Focus
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Preferred.Compiler

import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Decision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Decision

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (members : List Party)
  (depth count prefixLimit renewalLimit : Nat)

inductive Cause (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Type
  | migration (issue : Material.Migration.Obstruction input origin current.raw members prefixLimit renewalLimit)
  | renewal (word : RawEvent Party Good Port Technology Instrument)
      (issue : Review.Guarded.Issue input origin current.raw members word)

def Cause.focus {current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} :
    Cause input origin members prefixLimit renewalLimit current → Repair.Focus (Party := Party) (Good := Good) (Port := Port)
  | .migration issue => Focus.obstructionFocus input origin members prefixLimit renewalLimit issue
  | .renewal _ issue => Focus.guardedFocus input origin members issue

inductive Operation (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Type
  | migration (plan : Material.Migration.Plan input origin current.raw members prefixLimit renewalLimit)
      (source : Material.Migration.Preferred.compile input origin current.raw members prefixLimit renewalLimit = .accepted plan)
  | renewal (word : RawEvent Party Good Port Technology Instrument)
      (phase : current.phase = .renewal word)
      (checked : Review.Guarded.Checks input origin current.raw members word)
  | repair (cause : Cause input origin members prefixLimit renewalLimit current)
      (attempt : Repair.AttemptAt input depth count current.raw (cause.focus input origin members prefixLimit renewalLimit) current.remaining)

structure Obstruction (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) where
  cause : Cause input origin members prefixLimit renewalLimit current
  exhausted : ∀ request ∈ current.remaining,
    ¬ Repair.Relevant input depth count current.raw (cause.focus input origin members prefixLimit renewalLimit) request

inductive Outcome (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Type
  | action (operation : Operation input origin members depth count prefixLimit renewalLimit current)
  | blocked (issue : Obstruction input origin members depth count prefixLimit renewalLimit current)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Decision
