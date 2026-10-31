import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Submission
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Primitive
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Batch.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Migration.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Code

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

structure AutomaticAt where
  private mk ::
  operation : Operation input depth count prefixLimit renewalLimit current
  source_exact : decide input depth count prefixLimit renewalLimit current = .action operation

def automatic? : Option (AutomaticAt input depth count prefixLimit renewalLimit current) :=
  match produced : decide input depth count prefixLimit renewalLimit current with
  | .action operation => some ⟨operation, produced⟩
  | .blocked _ => none

inductive Dispatch : Type
  | automatic (generated : AutomaticAt input depth count prefixLimit renewalLimit current)
  | refusal (obstruction : ExactObstruction input depth count prefixLimit renewalLimit current)
      (source_exact : decide input depth count prefixLimit renewalLimit current = .blocked obstruction)

def dispatch : Dispatch input depth count prefixLimit renewalLimit current :=
  match produced : decide input depth count prefixLimit renewalLimit current with
  | .action operation => .automatic ⟨operation, produced⟩
  | .blocked obstruction => .refusal obstruction produced

structure SubmissionCheckAt (submission : Submission Party Good Port Technology Instrument) where
  private mk ::
  submitted : Submission Party Good Port Technology Instrument
  code_exact : submitted = submission
  source_admits : (receive input depth count prefixLimit renewalLimit current).admissible input depth count prefixLimit renewalLimit

def submissionCheck? (submission : Submission Party Good Port Technology Instrument) :
    Option (SubmissionCheckAt input depth count prefixLimit renewalLimit current submission) :=
  if admitted : (receive input depth count prefixLimit renewalLimit current).admissible input depth count prefixLimit renewalLimit then
    some ⟨submission, rfl, admitted⟩
  else none

/-- A registration command is usable only after the inquiry layer binds
its raw submission to the original source input occurrence. -/
inductive Command : Type
  | automatic (generated : AutomaticAt input depth count prefixLimit renewalLimit current)
  | submission (raw : Submission Party Good Port Technology Instrument)
      (checked : SubmissionCheckAt input depth count prefixLimit renewalLimit current raw)
  | primitive (request : Request Party Good Port Technology Instrument) (checked : PrimitiveAt input current request)
  | execute (word : RawEvent Party Good Port Technology Instrument)
      (checked : Batch.Checks input (origin input depth count) current.raw (members input depth count) word)
  | migrate (pair : RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
      (checked : Migration.Checks input (origin input depth count) current.raw (members input depth count) pair)
  | review (raw : ReviewSource.Control.Code Party Good Port Technology Instrument)
      (admitted : (receive input depth count prefixLimit renewalLimit current).admissible input depth count prefixLimit renewalLimit)

def Command.next : Command input depth count prefixLimit renewalLimit current →
    State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  | .automatic generated => generated.operation.next input depth count prefixLimit renewalLimit
  | .submission raw _ => submissionTarget current raw
  | .primitive request _ => primitiveNext input current request
  | .execute word _ =>
      let after := input.law.next current.raw word
      ⟨after, .seeking, Repair.alphabet input after⟩
  | .migrate pair _ =>
      let after := input.law.next current.raw pair.1
      ⟨after, .renewal pair.2, Repair.alphabet input after⟩
  | .review _ _ => current

def Command.requests : Command input depth count prefixLimit renewalLimit current → RawEvent Party Good Port Technology Instrument
  | .automatic generated => generated.operation.word input depth count prefixLimit renewalLimit
  | .submission .. => []
  | .primitive request _ => [request]
  | .execute word _ => word
  | .migrate pair _ => pair.1
  | .review _ _ => []

def Command.execution (command : Command input depth count prefixLimit renewalLimit current) :=
  input.law.execute current.raw 0 (command.requests input depth count prefixLimit renewalLimit current)

def Command.nonfinancial : Command input depth count prefixLimit renewalLimit current → Prop
  | .primitive request _ => Settlement.NonFinancialRequest request
  | .execute word _ => Settlement.NonFinancial word
  | .migrate pair _ => Settlement.NonFinancial pair.1
  | _ => True

theorem command_preserves_original_claims (command : Command input depth count prefixLimit renewalLimit current)
    (safe : command.nonfinancial input depth count prefixLimit renewalLimit current) :
    (command.next input depth count prefixLimit renewalLimit current).raw.claims = current.raw.claims := by
  cases command with
  | automatic generated => exact generated.operation.original_claims_are_kept input depth count prefixLimit renewalLimit
  | submission raw checked => rfl
  | primitive request checked => exact primitive_nonfinancial_keeps_claims input current request safe
  | execute word checked => exact safe.next_claims input.law current.raw word
  | migrate pair checked => exact safe.next_claims input.law current.raw pair.1
  | review raw admitted => rfl

theorem command_whole_material_balance (command : Command input depth count prefixLimit renewalLimit current)
    (person : Party) (good : Good) :
    (command.next input depth count prefixLimit renewalLimit current).raw.stock person good +
        input.law.totalDebit (command.execution input depth count prefixLimit renewalLimit current).items person good =
      current.raw.stock person good +
        input.law.totalCredit (command.execution input depth count prefixLimit renewalLimit current).items person good := by
  cases command with
  | automatic generated => exact generated.operation.whole_material_balance input depth count prefixLimit renewalLimit person good
  | submission raw checked => rfl
  | primitive request checked => exact input.law.execute_material_balance current.raw 0 [request] person good
  | execute word checked => exact input.law.actual_next_material_balance current.raw word person good
  | migrate pair checked => exact input.law.actual_next_material_balance current.raw pair.1 person good
  | review raw admitted => rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual
