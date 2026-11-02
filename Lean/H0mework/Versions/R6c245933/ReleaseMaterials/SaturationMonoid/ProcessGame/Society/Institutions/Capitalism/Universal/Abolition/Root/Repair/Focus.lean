import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration.Readback

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Repair

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

structure Focus where
  cells : List (Party × Good)
  ports : List Port

private def requirements (current : RawCurrent Party Good Technology Instrument) (person : Party) : Focus (Party := Party) (Good := Good) (Port := Port) :=
  ⟨((input.law.necessities current person) ++ (input.law.mandatoryMaintenance current person)).map
    (fun lot => (person, lot.1)), []⟩

private def instruction (item : ExecutionItem Party Good Port Technology Instrument) : Focus (Party := Party) (Good := Good) (Port := Port) :=
  ⟨(input.law.debit item.before item.request).map Prod.fst,
    input.law.requiredPorts item.before item.request⟩

private def floorFocus {origin current : RawCurrent Party Good Technology Instrument}
    {members : List Party} {word : RawEvent Party Good Port Technology Instrument}
    (issue : Material.NeedFloorIssue input origin current members word) : Focus (Party := Party) (Good := Good) (Port := Port) :=
  ⟨[(issue.cell.1, issue.cell.2.2.1)], []⟩

def prefixFocus {current : RawCurrent Party Good Technology Instrument} {word : RawEvent Party Good Port Technology Instrument}
    (issue : Material.Migration.PrefixIssue input (Migration.origin input depth count) current
      (Migration.cohort input depth count) word) : Focus (Party := Party) (Good := Good) (Port := Port) :=
  match issue with
  | .refused item _ | .consentRequired item _ => instruction input item.val
  | .foreignDebit _ debit _ _ _ => ⟨[debit.1], []⟩
  | .necessity person _ _ | .maintenance person _ _ => requirements input current person
  | .originalFloor issue => floorFocus input issue
  | .financial .. | .opaquePolicy .. => ⟨[], []⟩

def periodFocus {current : RawCurrent Party Good Technology Instrument} {word : RawEvent Party Good Port Technology Instrument}
    (issue : Material.PeriodIssue input current (Migration.cohort input depth count) word) : Focus (Party := Party) (Good := Good) (Port := Port) :=
  match issue with
  | .refused item _ | .consentRequired item _ => instruction input item.val
  | .foreignDebit _ _ debit _ _ _ => ⟨[debit.1], []⟩
  | .unpaidNecessity person _ _ | .unpaidMaintenance person _ _ => requirements input current person
  | .localControl use _ => ⟨[], [use.port]⟩
  | .freshControl _ port .. => ⟨[], [port]⟩
  | .outputLoss person _ lot _ _ | .inputIncrease person _ lot _ _ | .maintenanceIncrease person _ lot _ _ =>
      ⟨[(person, lot.1)], []⟩
  | .opaquePolicy .. => ⟨[], []⟩

def guardedFocus {current : RawCurrent Party Good Technology Instrument} {word : RawEvent Party Good Port Technology Instrument}
    (issue : Review.Guarded.Issue input (Migration.origin input depth count) current
      (Migration.cohort input depth count) word) : Focus (Party := Party) (Good := Good) (Port := Port) :=
  match issue with
  | .financial .. => ⟨[], []⟩
  | .originalNeed issue => floorFocus input issue
  | .period issue => periodFocus input depth count issue

def renewalFocus {current : RawCurrent Party Good Technology Instrument} {word : RawEvent Party Good Port Technology Instrument}
    (issue : Material.Migration.RenewalIssue input (Migration.origin input depth count) current
      (Migration.cohort input depth count) word) : Focus (Party := Party) (Good := Good) (Port := Port) :=
  match issue with
  | .period issue => periodFocus input depth count issue
  | .floor issue => floorFocus input issue
  | .balance issue => match issue with
    | .unsupported .. => ⟨[], []⟩
    | .imbalance cell _ _ => ⟨[cell], []⟩
  | .unexplained item .. => instruction input item.val

def pairFocus {current : RawCurrent Party Good Technology Instrument}
    {pair : Material.Migration.CodePair Party Good Port Technology Instrument}
    (issue : Material.Migration.PairIssue input (Migration.origin input depth count) current
      (Migration.cohort input depth count) pair) : Focus (Party := Party) (Good := Good) (Port := Port) :=
  match issue with
  | .prefixFailure issue => prefixFocus input depth count issue
  | .renewal issue => renewalFocus input depth count issue

def obstructionFocus {current : RawCurrent Party Good Technology Instrument}
    (issue : Material.Migration.Obstruction input (Migration.origin input depth count) current
      (Migration.cohort input depth count) prefixLimit renewalLimit) : Focus (Party := Party) (Good := Good) (Port := Port) :=
  ⟨issue.diagnoses.flatMap (fun diagnosis => (pairFocus input depth count diagnosis.2).cells),
    issue.diagnoses.flatMap (fun diagnosis => (pairFocus input depth count diagnosis.2).ports)⟩

/-- This projection preserves a simulated diagnosis as a diagnosis. The
repair's separately generated raw trace is the only new occurrence. -/
def focusOf {current : RawCurrent Party Good Technology Instrument}
    (assessment : Migration.Assessment input depth count prefixLimit renewalLimit current) :
    Option (Focus (Party := Party) (Good := Good) (Port := Port)) :=
  match assessment with
  | .obstruction issue => some (obstructionFocus input depth count prefixLimit renewalLimit issue)
  | .prefix _ result => match result with
    | .accepted _ => none
    | .rejected issue => some (prefixFocus input depth count issue)
  | .renewal _ result => match result with
    | .accepted _ => none
    | .rejected issue => some (guardedFocus input depth count issue)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Repair
