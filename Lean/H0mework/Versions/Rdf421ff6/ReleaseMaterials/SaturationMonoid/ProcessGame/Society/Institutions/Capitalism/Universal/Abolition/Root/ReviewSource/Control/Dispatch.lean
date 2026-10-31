import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Flow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)

/-- All data are restrictions of the original consumed raw past. Neither
the caller's newest proposal nor a second context register can choose them. -/
inductive ReportAt : Type
  | unregistered (missing : recovered input depth count prefixLimit renewalLimit current = none)
  | unavailable (located : Located input depth count prefixLimit renewalLimit)
      (original : recovered input depth count prefixLimit renewalLimit current = some located)
      (issue : PreparationIssue input depth count prefixLimit renewalLimit located)
      (generated : prepare input depth count prefixLimit renewalLimit located = .stopped issue)
  | inspected (located : Located input depth count prefixLimit renewalLimit)
      (original : recovered input depth count prefixLimit renewalLimit current = some located)
      (prepared : Prepared input depth count prefixLimit renewalLimit located)
      (generated : prepare input depth count prefixLimit renewalLimit located = .ready prepared)
      (phase : View input depth count prefixLimit renewalLimit located prepared)
      (phaseExact : phase = atCursor input depth count prefixLimit renewalLimit located prepared current)

def report : ReportAt input depth count prefixLimit renewalLimit current :=
  match original : recovered input depth count prefixLimit renewalLimit current with
  | none => .unregistered original
  | some located =>
      match generated : prepare input depth count prefixLimit renewalLimit located with
      | .stopped issue => .unavailable located original issue generated
      | .ready prepared => .inspected located original prepared generated
          (atCursor input depth count prefixLimit renewalLimit located prepared current) rfl

inductive Action (Party Good Port Technology Instrument : Type)
  | inactive
  | execute (raw : Compile.RawInput Party Good Port Technology Instrument)
  | obstructed
  | materialPaid

def phaseAction (located : Located input depth count prefixLimit renewalLimit)
    (prepared : Prepared input depth count prefixLimit renewalLimit located)
    (phase : View input depth count prefixLimit renewalLimit located prepared) :
    Action Party Good Port Technology Instrument :=
  match phase.2 with
  | .stopped _ => .obstructed
  | .materialPaid .. => .materialPaid
  | _ => .execute (expectedRaw input depth count prefixLimit renewalLimit located prepared phase)

def ReportAt.action : ReportAt input depth count prefixLimit renewalLimit current →
    Action Party Good Port Technology Instrument
  | .unregistered _ => .inactive
  | .unavailable .. => .obstructed
  | .inspected located _ prepared _ phase _ => phaseAction input depth count prefixLimit renewalLimit located prepared phase

def action : Action Party Good Port Technology Instrument :=
  match recovered input depth count prefixLimit renewalLimit current with
  | none => .inactive
  | some located =>
      match prepare input depth count prefixLimit renewalLimit located with
      | .stopped _ => .obstructed
      | .ready prepared =>
          phaseAction input depth count prefixLimit renewalLimit located prepared
            (atCursor input depth count prefixLimit renewalLimit located prepared current)

theorem report_and_opcode_are_one_source_computation :
    (report input depth count prefixLimit renewalLimit current).action input depth count prefixLimit renewalLimit current =
      action input depth count prefixLimit renewalLimit current := by
  unfold report
  split
  next original => simp only [ReportAt.action, action, original]
  next located original =>
    split
    next issue generated => simp only [ReportAt.action, action, original, generated]
    next prepared generated => simp only [ReportAt.action, action, original, generated]

theorem without_an_actual_registration_the_ordinary_route_is_unchanged
    (absent : recovered input depth count prefixLimit renewalLimit current = none) :
    action input depth count prefixLimit renewalLimit current = .inactive := by
  simp only [action, absent]

theorem the_report_phase_is_the_same_actual_physical_past
    (located : Located input depth count prefixLimit renewalLimit)
    (original : recovered input depth count prefixLimit renewalLimit current = some located)
    (prepared : Prepared input depth count prefixLimit renewalLimit located) :
    (atCursor input depth count prefixLimit renewalLimit located prepared current).1.past = current.past :=
  recovered_phase_reads_the_same_actual_past input depth count prefixLimit renewalLimit located prepared current original

theorem unexecuted_proposals_cannot_replace_the_registered_control
    (proposal : Compile.RawInput Party Good Port Technology Instrument) :
    action input depth count prefixLimit renewalLimit (Physical.receive current proposal) =
      action input depth count prefixLimit renewalLimit current := rfl

/-- Both successful material execution and every typed stop retain this
original source row; no branch supplies a native terminal receipt. -/
def originalResponsibility := ProgrammeSource.sourceEntry input
  (Settlement.committedVisit input depth count).current .inherited

theorem original_native_responsibility_is_still_carried :
    ((ProgrammeLedger.evolution input (Settlement.committedVisit input depth count).current).destination
      (originalResponsibility input depth count)).1 =
      ProgrammeSource.targetEntry input (Settlement.committedVisit input depth count).current .inherited := by
  unfold originalResponsibility
  cases (Settlement.committedVisit input depth count).current <;> exact ProgrammeLedger.destination_exact input _ _

#print axioms report
#print axioms unexecuted_proposals_cannot_replace_the_registered_control
#print axioms original_native_responsibility_is_still_carried

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control
