import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Nonnegative

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

inductive Movement | transfer | settlement deriving DecidableEq

def movement? (request : Request Party Good Port Technology Instrument) : Option Movement :=
  match request.operation with
  | .transfer .. => some .transfer
  | .settle .. => some .settlement
  | _ => none

def movingDebit (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (kind : Movement) : Flow Party Good :=
  if movement? item.request = some kind then law.actualDebit item.before item.request else []

def movingCredit (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (kind : Movement) : Flow Party Good :=
  if movement? item.request = some kind then law.actualCredit item.before item.request else []

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (code : Programme.Submission (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def resource (channel : Channel) (party : Party) (good : Good) : ℚ :=
  ((Programme.items input before code).map fun item =>
    flowAt (actualPart (Physical.Public.interpreter input) item.before item.request channel) party good).sum

def cashOut (kind : Movement) (party : Party) (good : Good) : ℚ :=
  ((Programme.items input before code).map fun item =>
    flowAt (movingDebit (Physical.Public.interpreter input) item kind) party good).sum

def cashIn (kind : Movement) (party : Party) (good : Good) : ℚ :=
  ((Programme.items input before code).map fun item =>
    flowAt (movingCredit (Physical.Public.interpreter input) item kind) party good).sum

/-- Stocks, requests and obligations are read from the same actual fold.
They accompany costs; an unpaid need is not silently counted as a saving. -/
def residualClaim (instrument : Instrument) (debtor holder : Party) : ℚ :=
  (Programme.run input before code).raw.claims instrument debtor holder

def requiredNeeds (party : Party) : Bundle Good :=
  (Physical.Public.interpreter input).necessities (Programme.run input before code).raw party

def requiredMaintenance (party : Party) : Bundle Good :=
  (Physical.Public.interpreter input).mandatoryMaintenance (Programme.run input before code).raw party

theorem resource_append (first second : Programme.Submission (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (channel : Channel) (party : Party) (good : Good) :
    resource input before (first ++ second) channel party good =
      resource input before first channel party good + resource input (Programme.run input before first) second channel party good := by
  simp only [resource,Programme.items_append,List.map_append,List.sum_append]

attribute [local simp] movement? movingDebit movingCredit

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
