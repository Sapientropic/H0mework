import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Command

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

inductive RawInput (Party Good Port Technology Instrument : Type)
  | advance
  | code (submission : Actual.Submission Party Good Port Technology Instrument)
  | primitive (request : Request Party Good Port Technology Instrument)
  | execute (word : RawEvent Party Good Port Technology Instrument)
  | migrate (pair : RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
  | stopReview
  | review (code : ReviewSource.Control.Code Party Good Port Technology Instrument)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

inductive SourceAt : RawInput Party Good Port Technology Instrument →
    Actual.Command input depth count prefixLimit renewalLimit current → Type
  | advance (generated : Actual.AutomaticAt input depth count prefixLimit renewalLimit current) :
      SourceAt .advance (.automatic generated)
  | code (submission : Actual.Submission Party Good Port Technology Instrument)
      (checked : Actual.SubmissionCheckAt input depth count prefixLimit renewalLimit current submission) :
      SourceAt (.code submission) (.submission submission checked)
  | primitive (request : Request Party Good Port Technology Instrument)
      (legal : input.law.Valid current.raw request) :
      SourceAt (.primitive request) (.primitive request (Actual.primitive input current request))
  | execute (word : RawEvent Party Good Port Technology Instrument)
      (checked : Actual.Batch.Checks input (Actual.origin input depth count) current.raw (Actual.members input depth count) word) :
      SourceAt (.execute word) (.execute word checked)
  | migrate (pair : RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
      (checked : Actual.Migration.Checks input (Actual.origin input depth count) current.raw (Actual.members input depth count) pair) :
      SourceAt (.migrate pair) (.migrate pair checked)
  | review (code : ReviewSource.Control.Code Party Good Port Technology Instrument)
      (admitted : (Actual.receive input depth count prefixLimit renewalLimit current).admissible input depth count prefixLimit renewalLimit) :
      SourceAt (.review code) (.review code admitted)

inductive RefusalAt : RawInput Party Good Port Technology Instrument → Type
  | blocked (obstruction : Actual.ExactObstruction input depth count prefixLimit renewalLimit current)
      (source : Actual.decide input depth count prefixLimit renewalLimit current = .blocked obstruction) :
      RefusalAt .advance
  | busy (submission : Actual.Submission Party Good Port Technology Instrument)
      (operation : Actual.Operation input depth count prefixLimit renewalLimit current)
      (notBoundary : match operation with | .renewal .. => False | _ => True)
      (source : Actual.decide input depth count prefixLimit renewalLimit current = .action operation) :
      RefusalAt (.code submission)
  | invalid (request : Request Party Good Port Technology Instrument)
      (failed : ¬ input.law.Valid current.raw request) : RefusalAt (.primitive request)
  | batch (word : RawEvent Party Good Port Technology Instrument)
      (issue : Actual.Batch.Issue input (Actual.origin input depth count) current.raw (Actual.members input depth count) word) :
      RefusalAt (.execute word)
  | migration (pair : RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
      (issue : Actual.Migration.Issue input (Actual.origin input depth count) current.raw (Actual.members input depth count) pair) :
      RefusalAt (.migrate pair)
  /-- The dependent review report owns the original cause. This opcode
  answers it without a physical instruction or a completed-world claim. -/
  | reviewStopped : RefusalAt .stopReview
  | reviewBusy (code : ReviewSource.Control.Code Party Good Port Technology Instrument)
      (operation : Actual.Operation input depth count prefixLimit renewalLimit current)
      (notBoundary : match operation with | .renewal .. => False | _ => True)
      (source : Actual.decide input depth count prefixLimit renewalLimit current = .action operation) :
      RefusalAt (.review code)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile
