import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Path
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Financial.Return

/-! Actual appropriation of the original controlled output cell.  The
source checks distinguish performed consumption, paid technology investment,
output-funded retention, and actual claim-backed financial return.  None
requires title transfer, and a material supply chain never supplies a title. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

/-- The item carries its own original before-current; no local execution
is replayed from a different word's clock. -/
def performedAt (item : ExecutionItem Party Good Port Technology Instrument)
    (port : Port) (holder : Party) (good : Good) : Prop :=
  law.Valid item.before item.request ∧
  law.controller item.before.technology port = holder ∧
  item.request.signer = holder ∧ item.request.consents = [] ∧
  match item.request.operation with
  | .use bearer _ kind => bearer = holder ∧ (kind = .external ∨ kind = .investment) ∧
      0 < flowAt (law.actualDebit item.before item.request) holder good
  | _ => False

instance (item : ExecutionItem Party Good Port Technology Instrument)
    (port : Port) (holder : Party) (good : Good) : Decidable (performedAt law item port holder good) := by
  unfold performedAt
  cases item.request.operation <;> infer_instance

/-- The actual revision spends the original holder's goods and changes a
local productive capacity.  It does not assume that a future output occurs. -/
def investedAt (item : ExecutionItem Party Good Port Technology Instrument)
    (port : Port) (holder : Party) (paidGood growthGood : Good) : Prop :=
  law.Valid item.before item.request ∧
  law.controller item.before.technology port = holder ∧
  item.request.signer = holder ∧ item.request.consents = [] ∧
  match item.request.operation with
  | .revise operator target => operator = holder ∧
      0 < flowAt (law.actualDebit item.before item.request) holder paidGood ∧
      amount Good (law.technique item.before.technology holder).outputs growthGood <
        amount Good (law.technique target holder).outputs growthGood
  | _ => False

instance (item : ExecutionItem Party Good Port Technology Instrument)
    (port : Port) (holder : Party) (paidGood growthGood : Good) :
    Decidable (investedAt law item port holder paidGood growthGood) := by
  unfold investedAt
  cases item.request.operation <;> infer_instance

variable (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

def ownedOutput (access : AccessProposal law current word) : Prop :=
  access.mode = .acquired ∧ access.accessHolder = access.controller law current word

instance (access : AccessProposal law current word) : Decidable (ownedOutput law current word access) := by
  unfold ownedOutput
  infer_instance

/-- The identified production credit itself covers every actual debit of
this original cell and leaves a positive remainder.  An unrelated gift or
an old positive balance cannot meet this attribution check. -/
def retainedOutput (access : AccessProposal law current word) : Prop :=
  (match access.access.val.request.operation with
    | .produce operator => operator = access.accessHolder
    | _ => False) ∧
  law.controller (law.next current word).technology access.port = access.accessHolder ∧
  law.totalDebit ((law.rawItems current word).filter (fun item => access.access.val.index ≤ item.index))
      access.accessHolder access.accessGood <
    flowAt (law.actualCredit access.access.val.before access.access.val.request)
      access.accessHolder access.accessGood ∧
  access.access.val.before.stock access.accessHolder access.accessGood <
    (law.next current word).stock access.accessHolder access.accessGood

instance (access : AccessProposal law current word) : Decidable (retainedOutput law current word access) := by
  unfold retainedOutput
  cases access.access.val.request.operation <;> infer_instance

inductive Evidence
  | consumption (position : OriginalItem law current word)
  | investment (position : OriginalItem law current word) (growthGood : Good)
  | retention
  | routedConsumption (position : OriginalItem law current word) (good : Good)
      (route : List (RouteLeg law current word))
  | financialReturn (path : Financial.ReturnPath law current word)

def outputBasis (access : AccessProposal law current word) : Evidence law current word → Prop
  | .routedConsumption .. | .financialReturn .. => access.mode = .acquired
  | _ => ownedOutput law current word access

instance (access : AccessProposal law current word) (evidence : Evidence law current word) :
    Decidable (outputBasis law current word access evidence) := by
  cases evidence <;> unfold outputBasis <;> infer_instance

def evidenceChecks (access : AccessProposal law current word) : Evidence law current word → Prop
  | .consumption position => access.access.val.index ≤ position.val.index ∧
      performedAt law position.val access.port access.accessHolder access.accessGood
  | .investment position growthGood => access.access.val.index ≤ position.val.index ∧
      investedAt law position.val access.port access.accessHolder access.accessGood growthGood
  | .retention => retainedOutput law current word access
  | .routedConsumption position good route =>
      Follows law current word (access.accessHolder, access.accessGood) (access.access.val.index + 1)
        route (law.controller position.val.before.technology access.port, good) position.val.index ∧
      controlAlong law current word access.port access.recipient (access.accessHolder, access.accessGood) route ∧
      performedAt law position.val access.port (law.controller position.val.before.technology access.port) good
  | .financialReturn path => Financial.ReturnPath.Checks law current word access path

instance (access : AccessProposal law current word) (evidence : Evidence law current word) :
    Decidable (evidenceChecks law current word access evidence) := by
  cases evidence <;> unfold evidenceChecks <;> infer_instance

def financialAlignment (proposal : Proposal law current word) : Evidence law current word → Prop
  | .financialReturn path => Financial.ReturnPath.Aligned law current word path proposal.reciprocity
  | _ => True

instance (proposal : Proposal law current word) (evidence : Evidence law current word) :
    Decidable (financialAlignment law current word proposal evidence) := by
  cases evidence <;> unfold financialAlignment <;> infer_instance

def rawChecks (proposal : Proposal law current word) (evidence : Evidence law current word) : Prop :=
  proposal.disposal.allocations = [] ∧ outputBasis law current word proposal.access evidence ∧
    evidenceChecks law current word proposal.access evidence ∧ financialAlignment law current word proposal evidence

instance (proposal : Proposal law current word) (evidence : Evidence law current word) :
    Decidable (rawChecks law current word proposal evidence) := by
  unfold rawChecks
  infer_instance

omit [DecidableEq Port] in
theorem allocation_chain_cannot_supply_title (proposal : Proposal law current word)
    (evidence : Evidence law current word) (chain : proposal.disposal.allocations ≠ []) :
    ¬ rawChecks law current word proposal evidence := fun checked => chain checked.1

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem necessary_use_is_not_surplus (item : ExecutionItem Party Good Port Technology Instrument)
    (port : Port) (holder bearer : Party) (good : Good) (goods : Bundle Good)
    (operation : item.request.operation = .use bearer goods .necessity) :
    ¬ performedAt law item port holder good := by
  simp only [performedAt, operation, reduceCtorEq, or_self, false_and, and_false, not_false_eq_true]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus
