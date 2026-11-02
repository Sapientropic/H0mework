import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook.Cash

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Funding
open ResponsibilityLifecycle Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

def Checks (claim : Claim sources)
    (access : AccessProposal (DelayedFinancing.law sources claim) (DelayedFinancing.before sources claim) (DelayedFinancing.word sources claim)) : Prop :=
  access.Checks _ _ _ ∧ access.mode = .acquired ∧
  ActualSurplus.Financial.ReturnPath.Advance _ _ _ access ∧
  access.accessHolder = claim.2.holder ∧ access.accessGood = (sources claim.1).law.settlementUnit claim.2.instrument ∧
  access.access.val.index < claim.2.instruction.index ∧ 0 < claim.2.quantity

instance (claim : Claim sources)
    (access : AccessProposal (DelayedFinancing.law sources claim) (DelayedFinancing.before sources claim) (DelayedFinancing.word sources claim)) :
    Decidable (Checks sources claim access) := by unfold Checks; infer_instance

/-- Funding is already paid to the original creditor. It is not ownership of
that creditor's claim and promises no later acquisition or repayment. -/
structure Pending (claim : Claim sources) where
  private mk ::
  access : AccessProposal (DelayedFinancing.law sources claim) (DelayedFinancing.before sources claim) (DelayedFinancing.word sources claim)
  checked : Checks sources claim access

def compile (claim : Claim sources)
    (access : AccessProposal (DelayedFinancing.law sources claim) (DelayedFinancing.before sources claim) (DelayedFinancing.word sources claim)) :
    Option (Pending sources claim) :=
  if checked : Checks sources claim access then some ⟨access,checked⟩ else none

def origins (claim : Claim sources) : List (Pending sources claim) :=
  (Discovery.accesses (DelayedFinancing.law sources claim) (DelayedFinancing.before sources claim)
    (DelayedFinancing.word sources claim)).filterMap (compile sources claim)

namespace Pending
variable {sources} {claim : Claim sources} (funding : Pending sources claim)
def controller := funding.access.controller (DelayedFinancing.law sources claim)
  (DelayedFinancing.before sources claim) (DelayedFinancing.word sources claim)
def advance := flowAt ((sources claim.1).law.actualDebit funding.access.access.val.before funding.access.access.val.request)
  funding.controller funding.access.accessGood

omit [DecidableEq Port] in
theorem original_advance_and_issuance :
    funding.access.Checks _ _ _ ∧ ActualSurplus.Financial.ReturnPath.Advance _ _ _ funding.access ∧
    funding.access.accessHolder = claim.2.holder ∧
    funding.access.access.val.index < claim.2.instruction.index ∧ 0 < claim.2.quantity :=
  ⟨funding.checked.1,funding.checked.2.2.1,funding.checked.2.2.2.1,
    funding.checked.2.2.2.2.2.1,funding.checked.2.2.2.2.2.2⟩
omit [DecidableEq Port] in
theorem advance_positive : 0 < funding.advance := by
  have advanced := funding.checked.2.2.1
  unfold ActualSurplus.Financial.ReturnPath.Advance at advanced
  cases operation : funding.access.access.val.request.operation <;> simp [operation] at advanced
  rcases advanced with ⟨_,_,_,_,sender,_,_,positive,_⟩
  simpa only [advance,controller,sender] using positive

end Pending

variable {obligation : AdmittedObligation (vocabulary sources)} (boundary : Boundary sources obligation)

def Acquires (funding : Pending sources obligation.content) : Prop :=
  boundary.receipt.kind = .assignment ∧ boundary.receipt.sender = obligation.content.2.holder ∧
  boundary.receipt.recipient = funding.controller ∧ boundary.receipt.sender ≠ boundary.receipt.recipient ∧
  0 < AssignedFinancing.quantity sources boundary

instance (funding : Pending sources obligation.content) : Decidable (Acquires sources boundary funding) := by
  unfold Acquires
  cases boundary.receipt.kind <;> infer_instance

structure Acquisition where
  private mk ::
  funding : Pending sources obligation.content
  actual : Acquires sources boundary funding

def acquire (funding : Pending sources obligation.content) : Option (Acquisition sources boundary) :=
  if actual : Acquires sources boundary funding then some ⟨funding,actual⟩ else none

def acquisitions : List (Acquisition sources boundary) :=
  (origins sources obligation.content).filterMap (acquire sources boundary)

theorem every_actual_acquisition_is_generated (funding : Pending sources obligation.content)
    (listed : funding ∈ origins sources obligation.content) (actual : Acquires sources boundary funding) :
    ∃ result ∈ acquisitions sources boundary, result.funding = funding := by
  refine ⟨⟨funding,actual⟩,List.mem_filterMap.mpr ⟨funding,listed,?_⟩,rfl⟩
  exact dif_pos actual

def initial (claim : Claim sources) : Share.Split (initialBalance (sources claim.1) claim.2) :=
  if (origins sources claim).isEmpty then FinancingBook.initial sources claim else
    ⟨initialBalance (sources claim.1) claim.2,0,initial_nonnegative _ _,fun _ => le_rfl,add_zero _⟩

theorem initial_positive_has_original_funding_or_direct_control (claim : Claim sources) (party : Party)
    (positive : 0 < (initial sources claim).selected party) :
    Nonempty (Pending sources claim) ∨ Nonempty (DelayedFinancing.Open sources claim) := by
  cases generated : origins sources claim with
  | nil =>
    apply Or.inr
    apply FinancingBook.initial_positive_has_its_source sources claim party
    simpa only [initial,generated,List.isEmpty_nil,if_true] using positive
  | cons head rest => exact Or.inl ⟨head⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Funding
