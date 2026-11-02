import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Exposure
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting.Balance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.Detector
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Financial.Return

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.DelayedFinancing
open ResponsibilityLifecycle Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev law (claim : Claim sources) := (sources claim.1).law
abbrev before (claim : Claim sources) := ProgrammeSource.rawCurrent (sources claim.1) claim.2.origin.visit.current
abbrev word (claim : Claim sources) := ProgrammeSource.rawEvent (sources claim.1) claim.2.origin.visit.current

def issuance (claim : Claim sources) : OriginalItem (law sources claim) (before sources claim) (word sources claim) :=
  ⟨claim.2.instruction,claim.2.original_inventory_provenance _⟩

def proposal (claim : Claim sources)
    (access : AccessProposal (law sources claim) (before sources claim) (word sources claim))
    (disposal : DisposalProposal (law sources claim) (before sources claim) (word sources claim)) :=
  (⟨access,.claim (issuance sources claim),disposal⟩ : Proposal (law sources claim) (before sources claim) (word sources claim))

def Checks (claim : Claim sources)
    (access : AccessProposal (law sources claim) (before sources claim) (word sources claim))
    (disposal : DisposalProposal (law sources claim) (before sources claim) (word sources claim)) : Prop :=
  (proposal sources claim access disposal).Checks (law sources claim) (before sources claim) (word sources claim) ∧
    disposal.allocations = [] ∧ access.mode = .acquired ∧
    ActualSurplus.Financial.ReturnPath.Advance (law sources claim) (before sources claim) (word sources claim) access ∧
    access.accessHolder = claim.2.debtor ∧
    access.accessGood = (law sources claim).settlementUnit claim.2.instrument

instance (claim : Claim sources)
    (access : AccessProposal (law sources claim) (before sources claim) (word sources claim))
    (disposal : DisposalProposal (law sources claim) (before sources claim) (word sources claim)) :
    Decidable (Checks sources claim access disposal) := by unfold Checks; infer_instance

/-- The original controlled financing relation is checked before any return is required. -/
structure Open (claim : Claim sources) where
  private mk ::
  access : AccessProposal (law sources claim) (before sources claim) (word sources claim)
  disposal : DisposalProposal (law sources claim) (before sources claim) (word sources claim)
  checked : Checks sources claim access disposal

def compile (claim : Claim sources)
    (access : AccessProposal (law sources claim) (before sources claim) (word sources claim))
    (disposal : DisposalProposal (law sources claim) (before sources claim) (word sources claim)) : Option (Open sources claim) :=
  if checked : Checks sources claim access disposal then some ⟨access,disposal,checked⟩ else none

def origins (claim : Claim sources) : List (Open sources claim) :=
  (Discovery.accesses (law sources claim) (before sources claim) (word sources claim)).flatMap fun access =>
    (Discovery.disposals (law sources claim) (before sources claim) (word sources claim) access).filterMap
      (compile sources claim access)

namespace Open
variable {sources} {claim : Claim sources} (origin : Open sources claim)

def dependency : CapitalRelationKernel (law sources claim) (before sources claim) (word sources claim) :=
  (Source.ProgrammeControl.Kernel.compile _ _ _ (proposal sources claim origin.access origin.disposal)).get
    (by simp only [Source.ProgrammeControl.Kernel.compile,dif_pos origin.checked.1,Option.isSome_some])

def holder := origin.access.controller (law sources claim) (before sources claim) (word sources claim)
def good := origin.access.accessGood
def advance : ℚ := flowAt ((law sources claim).actualDebit origin.access.access.val.before origin.access.access.val.request)
  origin.holder origin.good

omit [DecidableEq Port] in
theorem original_control_and_disposal :
    (proposal sources claim origin.access origin.disposal).Checks (law sources claim) (before sources claim) (word sources claim) ∧
    origin.disposal.allocations = [] ∧
    ActualSurplus.Financial.ReturnPath.Advance (law sources claim) (before sources claim) (word sources claim) origin.access :=
  ⟨origin.checked.1,origin.checked.2.1,origin.checked.2.2.2.1⟩
end Open

variable {first last : ResponsibilityState (vocabulary sources)} {run : (process sources).Run first last}
  (birth : Exposure.Birth sources run)

def recovered (origin : Open sources birth.claim) : ℚ :=
  ((birth.follow.path.events sources).map fun event => Posting.amount sources event .credit origin.holder origin.good).sum

def asset (origin : Open sources birth.claim) : ℚ := Posting.Balance.slot sources birth.follow.slot .credit origin.holder origin.good

def netRecovery (origin : Open sources birth.claim) : ℚ := recovered sources birth origin + asset sources birth origin - origin.advance

structure Returned where
  private mk ::
  origin : Open sources birth.claim
  positive : 0 < recovered sources birth origin

def reports : List (Returned sources birth) := (origins sources birth.claim).filterMap fun origin =>
  if positive : 0 < recovered sources birth origin then some ⟨origin,positive⟩ else none

theorem every_checked_origin_with_an_actual_return_is_generated (origin : Open sources birth.claim)
    (listed : origin ∈ origins sources birth.claim) (positive : 0 < recovered sources birth origin) :
    ∃ report ∈ reports sources birth, report.origin = origin := by
  refine ⟨⟨origin,positive⟩,List.mem_filterMap.mpr ⟨origin,listed,?_⟩,rfl⟩
  exact dif_pos positive

theorem every_report_has_a_positive_actual_allocation (report : Returned sources birth) :
    ∃ event ∈ birth.follow.path.events sources,
      event.claim sources = birth.claim ∧ 0 < Posting.amount sources event .credit report.origin.holder report.origin.good := by
  have positive := report.positive
  have findPositive (events : List (Event sources))
      (paid : 0 < (events.map fun event => Posting.amount sources event .credit report.origin.holder report.origin.good).sum) :
      ∃ event ∈ events, 0 < Posting.amount sources event .credit report.origin.holder report.origin.good := by
    induction events with
    | nil => simp only [List.map_nil,List.sum_nil,lt_self_iff_false] at paid
    | cons event rest ih =>
        by_cases head : 0 < Posting.amount sources event .credit report.origin.holder report.origin.good
        · exact ⟨event,List.mem_cons_self,head⟩
        · have tail : 0 < (rest.map fun event => Posting.amount sources event .credit report.origin.holder report.origin.good).sum := by
            simp only [List.map_cons,List.sum_cons] at paid; linarith
          obtain ⟨later,member,positive⟩ := ih tail
          exact ⟨later,List.mem_cons_of_mem _ member,positive⟩
  obtain ⟨event,member,paid⟩ := findPositive _ positive
  exact ⟨event,member,(birth.follow.path.events_preserve_original_claim sources event member),paid⟩

theorem principal_and_actual_return_are_not_double_counted (origin : Open sources birth.claim) :
    birth.remaining + birth.paid = birth.claim.2.quantity ∧
    netRecovery sources birth origin = recovered sources birth origin + asset sources birth origin - origin.advance :=
  ⟨birth.conservation,rfl⟩

/-- Stable native slot indices select a cohort without comparing source functions. -/
def marked (births : List (Exposure.Birth sources run)) (index : Nat) : Bool :=
  births.any fun birth => birth.index == index && !(reports sources birth).isEmpty

theorem marked_exact (births : List (Exposure.Birth sources run)) (index : Nat) :
    marked sources births index = true ↔
      ∃ birth ∈ births, birth.index = index ∧ (reports sources birth).isEmpty = false := by
  simp only [marked,List.any_eq_true,Bool.and_eq_true,beq_iff_eq]
  have negated (value : Bool) : (!value) = true ↔ value = false := by cases value <;> decide
  simp only [negated]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.DelayedFinancing
