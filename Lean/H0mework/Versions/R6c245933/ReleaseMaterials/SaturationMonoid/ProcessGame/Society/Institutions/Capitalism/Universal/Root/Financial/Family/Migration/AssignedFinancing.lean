import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Share
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.DelayedFinancing

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.AssignedFinancing
open ResponsibilityLifecycle Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev law {claim : Claim sources} (review : Review sources claim) := (sources review.origin.1).law
abbrev before {claim : Claim sources} (review : Review sources claim) :=
  ProgrammeSource.rawCurrent (sources review.origin.1) review.origin.2.visit.current
abbrev word {claim : Claim sources} (review : Review sources claim) :=
  ProgrammeSource.rawEvent (sources review.origin.1) review.origin.2.visit.current

def original {claim : Claim sources} (review : Review sources claim) :
    OriginalItem (law sources review) (before sources review) (word sources review) :=
  ⟨review.instruction,review.origin.2.instruction_mem _ _ review.original⟩

def proposal {claim : Claim sources} (review : Review sources claim)
    (access : AccessProposal (law sources review) (before sources review) (word sources review))
    (disposal : DisposalProposal (law sources review) (before sources review) (word sources review)) :=
  (⟨access,.claim (original sources review),disposal⟩ : Proposal (law sources review) (before sources review) (word sources review))

def quantity {obligation : AdmittedObligation (vocabulary sources)} (boundary : Boundary sources obligation) : ℚ :=
  min boundary.cap (obligation.residual boundary.receipt.sender)

private instance : DecidableEq MovementKind := fun left right => by
  cases left <;> cases right <;> first | exact isTrue rfl | exact isFalse (by intro same; cases same)

def Checks {obligation : AdmittedObligation (vocabulary sources)} (boundary : Boundary sources obligation)
    (access : AccessProposal (law sources boundary.receipt) (before sources boundary.receipt) (word sources boundary.receipt))
    (disposal : DisposalProposal (law sources boundary.receipt) (before sources boundary.receipt) (word sources boundary.receipt)) : Prop :=
  (proposal sources boundary.receipt access disposal).Checks _ _ _ ∧
  disposal.allocations = [] ∧ access.mode = .acquired ∧
  ActualSurplus.Financial.ReturnPath.Advance _ _ _ access ∧
  access.accessHolder = boundary.receipt.sender ∧
  access.accessGood = (sources obligation.content.1).law.settlementUnit obligation.content.2.instrument ∧
  boundary.receipt.kind = .assignment ∧ boundary.receipt.sender ≠ boundary.receipt.recipient ∧
  access.controller _ _ _ = boundary.receipt.recipient ∧ 0 < quantity sources boundary

instance {obligation : AdmittedObligation (vocabulary sources)} (boundary : Boundary sources obligation)
    (access : AccessProposal (law sources boundary.receipt) (before sources boundary.receipt) (word sources boundary.receipt))
    (disposal : DisposalProposal (law sources boundary.receipt) (before sources boundary.receipt) (word sources boundary.receipt)) :
    Decidable (Checks sources boundary access disposal) := by unfold Checks; infer_instance

structure Open {obligation : AdmittedObligation (vocabulary sources)} (boundary : Boundary sources obligation) where
  private mk ::
  access : AccessProposal (law sources boundary.receipt) (before sources boundary.receipt) (word sources boundary.receipt)
  disposal : DisposalProposal (law sources boundary.receipt) (before sources boundary.receipt) (word sources boundary.receipt)
  checked : Checks sources boundary access disposal

def compile {obligation : AdmittedObligation (vocabulary sources)} (boundary : Boundary sources obligation)
    (access : AccessProposal (law sources boundary.receipt) (before sources boundary.receipt) (word sources boundary.receipt))
    (disposal : DisposalProposal (law sources boundary.receipt) (before sources boundary.receipt) (word sources boundary.receipt)) :
    Option (Open sources boundary) :=
  if checked : Checks sources boundary access disposal then some ⟨access,disposal,checked⟩ else none

def origins {obligation : AdmittedObligation (vocabulary sources)} (boundary : Boundary sources obligation) :
    List (Open sources boundary) :=
  (Discovery.accesses (law sources boundary.receipt) (before sources boundary.receipt) (word sources boundary.receipt)).flatMap fun access =>
    (Discovery.disposals (law sources boundary.receipt) (before sources boundary.receipt) (word sources boundary.receipt) access).filterMap
      (compile sources boundary access)

namespace Open
variable {sources} {obligation : AdmittedObligation (vocabulary sources)} {boundary : Boundary sources obligation}
  (origin : Open sources boundary)

def dependency : CapitalRelationKernel (law sources boundary.receipt) (before sources boundary.receipt) (word sources boundary.receipt) :=
  (Kernel.compile _ _ _ (proposal sources boundary.receipt origin.access origin.disposal)).get
    (by simp only [Kernel.compile,dif_pos origin.checked.1,Option.isSome_some])

theorem assignment (origin : Open sources boundary) : boundary.receipt.kind = .assignment := origin.checked.2.2.2.2.2.2.1
theorem positive (origin : Open sources boundary) : 0 < quantity sources boundary := origin.checked.2.2.2.2.2.2.2.2.2

/-- Only the actually acquired quantity is newly selected. Existing holdings,
including any prior holding at the recipient, stay in the other component. -/
def acquired : Share.Split (slotBalance sources (Boundary.disposition sources boundary).targetSlot) := by
  refine Share.Split.reindex (balance := (boundary.event sources).after sources)
    ⟨initialShare (sources obligation.content.1) boundary.receipt.recipient (quantity sources boundary),
    pay (sources obligation.content.1) obligation.residual boundary.receipt.sender (quantity sources boundary),?_,?_,?_⟩ (boundary_balance sources boundary).symm
  · intro party
    rw [initialShare_eq_single, Finsupp.single_apply]
    split_ifs
    · exact le_of_lt origin.positive
    · exact le_rfl
  · exact pay_nonnegative _ _ _ _ boundary.nonnegative (min_le_right _ _)
  · apply Finsupp.ext
    intro party
    simp only [Finsupp.add_apply,initialShare_eq_single,Finsupp.single_apply,pay_apply,
      Family.Event.after,Boundary.event,Review.after,origin.assignment,assign_apply,quantity]
    by_cases recipient : party = boundary.receipt.recipient <;>
      by_cases sender : party = boundary.receipt.sender <;> simp [recipient,sender,eq_comm] <;> ring

theorem acquired_total :
    Financial.total (sources obligation.content.1) origin.acquired.selected = quantity sources boundary := by
  change Financial.total (sources obligation.content.1)
    (initialShare (sources obligation.content.1) boundary.receipt.recipient (quantity sources boundary)) = _
  rw [initialShare_eq_single]
  exact Finsupp.sum_single_index rfl

end Open

structure Occurrence {first last : ObligationSlot (vocabulary sources)} (path : Path sources first last) where
  private mk ::
  obligation : AdmittedObligation (vocabulary sources)
  prior : Path sources first (.live obligation)
  boundary : Boundary sources obligation
  suffix : Path sources (Boundary.disposition sources boundary).targetSlot last
  exact_records : ∀ index, path.records sources index = prior.records sources index ++
    [record sources index boundary] ++ suffix.records sources index

namespace Occurrence
variable {sources} {first last : ObligationSlot (vocabulary sources)} {path : Path sources first last}

def extend (occurrence : Occurrence sources path)
    {obligation : AdmittedObligation (vocabulary sources)} (boundary : Boundary sources obligation)
    (same : last = .live obligation) : Occurrence sources (Path.snoc (same ▸ path) boundary) := by
  subst last
  exact ⟨occurrence.obligation,occurrence.prior,occurrence.boundary,.snoc occurrence.suffix boundary,
    fun index => by simp only [Path.records,occurrence.exact_records,List.append_assoc]⟩

def fresh {obligation : AdmittedObligation (vocabulary sources)}
    (prior : Path sources first (.live obligation)) (boundary : Boundary sources obligation) :
    Occurrence sources (.snoc prior boundary) :=
  ⟨obligation,prior,boundary,.nil _,fun _ => (List.append_nil _).symm⟩

theorem same_claim (occurrence : Occurrence sources path) :
    occurrence.obligation.content = slotClaim sources first := occurrence.prior.preserves_claim sources

theorem actual_record (occurrence : Occurrence sources path) (index : Nat) :
    record sources index occurrence.boundary ∈ path.records sources index := by
  rw [occurrence.exact_records]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
end Occurrence

def occurrences {first last : ObligationSlot (vocabulary sources)}
    (path : Path sources first last) : List (Occurrence sources path) :=
  match path with
  | .nil _ => []
  | .snoc prior boundary =>
      (occurrences prior).map (fun occurrence => occurrence.extend boundary rfl) ++ [Occurrence.fresh prior boundary]

structure Report {first last : ObligationSlot (vocabulary sources)} (path : Path sources first last) where
  private mk ::
  occurrence : Occurrence sources path
  origin : Open sources occurrence.boundary

def reports {first last : ObligationSlot (vocabulary sources)}
    (path : Path sources first last) : List (Report sources path) :=
  (occurrences sources path).flatMap fun occurrence =>
    (origins sources occurrence.boundary).map fun origin => ⟨occurrence,origin⟩

namespace Report
variable {sources} {first last : ObligationSlot (vocabulary sources)} {path : Path sources first last}
  (report : Report sources path)

def flow := Share.transport sources report.occurrence.suffix report.origin.acquired

theorem actual_original_assignment (index : Nat) :
    record sources index report.occurrence.boundary ∈ path.records sources index ∧
    report.occurrence.obligation.content = slotClaim sources first ∧
    report.occurrence.boundary.receipt.kind = .assignment ∧ 0 < quantity sources report.occurrence.boundary :=
  ⟨report.occurrence.actual_record index,report.occurrence.same_claim,report.origin.assignment,report.origin.positive⟩

theorem exact_remaining_shares (party : Party) :
    report.flow.final.selected party + report.flow.final.remainder party = slotBalance sources last party :=
  report.flow.final.pointwise party

theorem actual_acquisition_is_not_reissued_or_counted_twice :
    Financial.total (sources report.occurrence.obligation.content.1) report.flow.final.selected + report.flow.selectedPaid =
      quantity sources report.occurrence.boundary := by
  exact (report.flow.selected_conservation report.occurrence.obligation.content.1).trans report.origin.acquired_total

end Report
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.AssignedFinancing
