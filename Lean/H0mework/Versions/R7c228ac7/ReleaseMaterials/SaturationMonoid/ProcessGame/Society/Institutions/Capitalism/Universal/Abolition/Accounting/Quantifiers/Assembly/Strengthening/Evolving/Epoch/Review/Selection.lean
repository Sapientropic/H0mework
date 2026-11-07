import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Control
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Fees.Parse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Migration.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Review

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument) (members : List Party)
  (cursor : ReviewCursor (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

inductive Selection : Type
  | renewal (word : RawEvent Party Good Port Technology Instrument)
      (original : cursor.renewalDue = some word)
      (checked : Abolition.Review.Guarded.Checks input origin current members word)
  | renewalBlocked (word : RawEvent Party Good Port Technology Instrument)
      (original : cursor.renewalDue = some word)
      (issue : Abolition.Review.Guarded.Issue input origin current members word)
  | halted (original : cursor.halted = true)
  | exhausted (original : cursor.remaining = [])
  | invalidFee (original : ReviewSource.Fees.scope? cursor.code.fee = none)
  | fee (scope : Abolition.Review.FeeScope cursor.code.fee)
      (parsed : ReviewSource.Fees.scope? cursor.code.fee = some scope)
  | candidate (pair : RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
      (tail : List (RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument))
      (original : cursor.remaining = pair :: tail)
      (checked : Actual.Migration.Checks input origin current members pair)
  | rejected (pair : RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
      (tail : List (RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument))
      (original : cursor.remaining = pair :: tail)
      (issue : Actual.Migration.Issue input origin current members pair)

def compile : Selection input origin current members cursor :=
  if halted : cursor.halted = true then .halted halted
  else match renewal : cursor.renewalDue with
  | some word => match Abolition.Review.Guarded.inspect input origin current members word with
    | .accepted checked => .renewal word renewal checked
    | .rejected issue => .renewalBlocked word renewal issue
  | none => match original : cursor.remaining with
    | [] => .exhausted original
    | pair :: tail =>
        if cursor.feePaid then
          match Actual.Migration.inspect input origin current members pair with
          | .accepted checked => .candidate pair tail original checked
          | .refused issue => .rejected pair tail original issue
        else match parsed : ReviewSource.Fees.scope? cursor.code.fee with
          | none => .invalidFee parsed
          | some scope => .fee scope parsed

namespace Selection
variable {input origin current members cursor}

def executionRaw : Selection input origin current members cursor → Compile.RawInput Party Good Port Technology Instrument
  | .fee scope _ => .primitive (ReviewSource.Fees.originalCode scope).withoutConsents.request
  | .candidate pair _ _ _ => .execute pair.1
  | .renewal word _ _ => .execute word
  | _ => .stopReview

end Selection
attribute [local simp] compile Selection.executionRaw

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Review
