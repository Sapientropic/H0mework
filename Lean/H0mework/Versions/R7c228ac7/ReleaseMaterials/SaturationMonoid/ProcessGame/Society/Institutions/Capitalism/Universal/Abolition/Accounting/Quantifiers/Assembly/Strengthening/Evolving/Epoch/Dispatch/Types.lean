import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Control
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Migration.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Dispatch

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (members : List Party)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

inductive Selection : Compile.RawInput Party Good Port Technology Instrument → Type
  | automatic (operation : Decision.Operation input origin members depth count prefixLimit renewalLimit current)
      (source : Decision.compile input origin members depth count prefixLimit renewalLimit current = .action operation) : Selection .advance
  | exhausted (issue : Decision.Obstruction input origin members depth count prefixLimit renewalLimit current)
      (source : Decision.compile input origin members depth count prefixLimit renewalLimit current = .blocked issue) : Selection .advance
  | code (submission : Actual.Submission Party Good Port Technology Instrument)
      (admitted : boundary input origin members depth count prefixLimit renewalLimit current) : Selection (.code submission)
  | codeBusy (submission : Actual.Submission Party Good Port Technology Instrument)
      (busy : ¬ boundary input origin members depth count prefixLimit renewalLimit current) : Selection (.code submission)
  | review (code : ReviewSource.Control.Code Party Good Port Technology Instrument)
      (admitted : boundary input origin members depth count prefixLimit renewalLimit current) : Selection (.review code)
  | reviewBusy (code : ReviewSource.Control.Code Party Good Port Technology Instrument)
      (busy : ¬ boundary input origin members depth count prefixLimit renewalLimit current) : Selection (.review code)
  | migrate (pair : RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
      (checked : Actual.Migration.Checks input origin current.raw members pair) : Selection (.migrate pair)
  | migrationBlocked (pair : RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
      (issue : Actual.Migration.Issue input origin current.raw members pair) : Selection (.migrate pair)
  | primitive (request : Request Party Good Port Technology Instrument) : Selection (.primitive request)
  | execute (word : RawEvent Party Good Port Technology Instrument) : Selection (.execute word)
  | stopped : Selection .stopReview

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Dispatch
