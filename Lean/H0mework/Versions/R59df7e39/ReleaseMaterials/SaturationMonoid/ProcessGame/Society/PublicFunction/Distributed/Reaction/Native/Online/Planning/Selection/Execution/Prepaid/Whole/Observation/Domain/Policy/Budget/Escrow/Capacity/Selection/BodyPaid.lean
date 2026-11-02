import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Bound.Body
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Paid
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.CandidatePayment
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

-- Every candidate freezes its source after its own actual reservation.
structure Release (prepared : Prepared input) (units : Nat) where
  private mk ::
  paid : PaidSelection.Funded prepared units
  actual : PaidSelection.Available paid.family
  covered : Body.units actual.pool + Work.workBudget actual.pool ≤ units
  body : Body.Generated actual.pool
  body_generated : body = Body.generate actual.pool
  work : Work.Generated actual.pool
  work_generated : work = Work.generate actual.pool

inductive Outcome (prepared : Prepared input) (units : Nat) where
  | unfunded (why : PaidSelection.Failure prepared units)
  | unavailable (paid : PaidSelection.Funded prepared units)
      (source : SourceQuota.Generated paid.family) (why : PaidSelection.NoDomain source)
  | shortfall (paid : PaidSelection.Funded prepared units) (actual : PaidSelection.Available paid.family)
      (lacks : units < Body.units actual.pool + Work.workBudget actual.pool)
  | released (made : Release prepared units)

-- The source-only guard precedes construction of either completed work receipt.
def execute (prepared : Prepared input) (units : Nat) : Outcome prepared units :=
  match PaidSelection.pay prepared units with
  | .failed why => .unfunded why
  | .paid paid => match PaidSelection.acquire paid.family with
    | .missing source why => .unavailable paid source why
    | .ready actual =>
      if covered : Body.units actual.pool + Work.workBudget actual.pool ≤ units then
        .released ⟨paid,actual,covered,Body.generate actual.pool,rfl,Work.generate actual.pool,rfl⟩
      else .shortfall paid actual (Nat.lt_of_not_ge covered)

namespace Release
variable {units : Nat} (made : Release prepared units)
theorem original_body_is_used : made.body.budget = Bound.generate made.actual.pool := by
  rw [made.body_generated];rfl
theorem original_selection_is_used : made.work = Work.generate made.actual.pool := made.work_generated

theorem body_fits : made.body.budget.work.length ≤ Body.units made.actual.pool := by
  rw [made.body_generated]
  exact Body.generated_body_fits_the_source_units _
theorem selection_fits : made.work.work.length ≤ Work.workBudget made.actual.pool := by
  rw [made.work_generated]
  have bounded := Body.source_body_and_full_selection_fit_the_joint_source_allowance made.actual.pool
  exact Work.receipt_work_fits_the_source_budget made.actual.pool (sections made.actual.pool) (List.Perm.refl _) (Work.generate made.actual.pool).receipt

theorem complete_body_and_selection_fit_the_same_prepaid_invoice :
    made.body.budget.work.length + made.work.work.length ≤ units :=
  (Nat.add_le_add made.body_fits made.selection_fits).trans made.covered

abbrev BodyOrdinal := Fin made.body.budget.work.length
abbrev SelectionOrdinal := Fin made.work.work.length
abbrev Token := Sum made.BodyOrdinal made.SelectionOrdinal

def ordinal : made.Token → Nat
  | .inl body => body.val
  | .inr selection => Body.units made.actual.pool + selection.val

theorem ordinal_bound (token : made.Token) : made.ordinal token < units := by
  cases token with
  | inl body => have := body.isLt;have := made.body_fits;have := made.covered;dsimp [ordinal];omega
  | inr selection => have := selection.isLt;have := made.selection_fits;have := made.covered;dsimp [ordinal];omega

theorem ordinal_injective : Function.Injective made.ordinal := by
  intro first second same
  cases first with
  | inl first => cases second with
    | inl second => exact congrArg Sum.inl (Fin.ext same)
    | inr second => have := first.isLt;have := made.body_fits;dsimp [ordinal] at same;omega
  | inr first => cases second with
    | inl second => have := second.isLt;have := made.body_fits;dsimp [ordinal] at same;omega
    | inr second =>
      apply congrArg Sum.inr
      apply Fin.ext
      dsimp [ordinal] at same
      omega

def slot (index : Index prepared) (token : made.Token) :
    Fin (((made.paid.funding.resultAt index).invoice (made.paid.all_paid index)).bill.units) :=
  ⟨made.ordinal token,by rw [((made.paid.funding.resultAt index).invoice (made.paid.all_paid index)).size];exact made.ordinal_bound token⟩

theorem body_and_selection_cannot_reuse_any_invoice_slot (index : Index prepared) : Function.Injective (made.slot index) := by
  intro first second same
  exact made.ordinal_injective (congrArg (fun slot => slot.val) same)

inductive Event where
  | body (event : Bound.Event made.actual.pool)
  | selection (event : Work.Operation made.actual.pool)
def event : made.Token → made.Event
  | .inl body => .body made.body.budget.work[body]
  | .inr selection => .selection made.work.work[selection]

structure Allocation (index : Index prepared) (token : made.Token) where
  private mk ::
  invoice : EscrowBudget.Charge.Invoice (made.paid.funding.resultAt index)
  slot : Fin invoice.bill.units
  event : made.Event
  slot_exact : slot.val = made.ordinal token
  event_exact : event = made.event token

def allocation (index : Index prepared) (token : made.Token) : Allocation made index token :=
  ⟨(made.paid.funding.resultAt index).invoice (made.paid.all_paid index),made.slot index token,made.event token,rfl,rfl⟩

theorem every_budget_and_selection_event_reads_its_actual_paid_invoice (index : Index prepared) (token : made.Token) :
    (made.allocation index token).invoice.bill.payment.succeeded = true ∧
    (made.allocation index token).invoice.bill.units = units ∧
    (made.allocation index token).event = made.event token :=
  ⟨(made.allocation index token).invoice.paid,(made.allocation index token).invoice.size,rfl⟩

theorem every_original_point_order_and_multiplicity_survives :
    made.paid.family.saved.map Cell.point = prepared.saved.map Cell.point :=
  made.paid.funding.source_order_and_multiplicity

def unused := units - (made.body.budget.work.length + made.work.work.length)
theorem every_credit_is_used_once_or_retained :
    made.body.budget.work.length + made.work.work.length + made.unused = units := by
  have := made.complete_body_and_selection_fit_the_same_prepaid_invoice
  unfold unused
  omega
end Release

inductive Debt where
  | prior (debt : PaidSelection.Debt (input := input))
  | counter {family : Prepared input} {snapshot : SourceQuota.Snapshot family} {catalogue : SourceQuota.Catalogue snapshot}
      (pool : Comparison.Pool catalogue)
  | quoteInternals
  | sourceService
  | primitiveInternals
  | ledgerInstallation
  | storage
  | announcement

def Outcome.pending {units : Nat} : Outcome prepared units → List (Debt (input := input))
  | .unfunded why => why.pending.map Debt.prior
  | .unavailable paid source _ =>
      (PaidSelection.fundingDebts paid.funding ++ source.pending.map PaidSelection.Debt.source).map Debt.prior
  | .shortfall paid actual _ =>
      (PaidSelection.fundingDebts paid.funding ++ actual.pending).map Debt.prior ++ [.counter actual.pool]
  | .released made =>
      (PaidSelection.fundingDebts made.paid.funding ++ made.actual.pending ++
        made.body.budget.work.map (PaidSelection.Debt.budget made.actual.pool) ++
        made.work.debts.map (PaidSelection.Debt.selection made.actual.pool made.work)).map Debt.prior ++ [.counter made.actual.pool]

structure Record (prepared : Prepared input) (units : Nat) where
  private mk ::
  outcome : Outcome prepared units
  generated : outcome = execute prepared units

def generate (prepared : Prepared input) (units : Nat) : Record prepared units := ⟨execute prepared units,rfl⟩
def Record.pending {units : Nat} (made : Record prepared units) : List (Debt (input := input)) :=
  (PaidSelection.originalDebts prepared).map Debt.prior ++ made.outcome.pending ++
    [.quoteInternals,.sourceService,.primitiveInternals,.ledgerInstallation,.storage,.announcement]
theorem every_original_debt_survives {units : Nat} (made : Record prepared units) (debt : Policy.Obligation prepared)
    (inside : debt ∈ Policy.obligations prepared) : Debt.prior (.original prepared debt) ∈ made.pending := by
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨debt,inside,rfl⟩,rfl⟩

-- These are alternative actual branches from the same source, not one history spending every quota.
structure Candidates {prepared : Prepared input} (source : SourceQuota.Generated prepared)
    (domain : SourceQuota.Catalogue source.snapshot) where
  private mk ::
  entries : List ((quota : domain.Quota) × Record prepared quota.val)
  generated : entries = domain.quotas.map (fun quota => ⟨quota,generate prepared quota.val⟩)

def candidates {prepared : Prepared input} (source : SourceQuota.Generated prepared)
    (domain : SourceQuota.Catalogue source.snapshot) : Candidates source domain :=
  ⟨domain.quotas.map (fun quota => ⟨quota,generate prepared quota.val⟩),rfl⟩

theorem every_source_quota_has_its_own_paid_candidate {source : SourceQuota.Generated prepared}
    {domain : SourceQuota.Catalogue source.snapshot} (made : Candidates source domain) (quota : domain.Quota) :
    ⟨quota,generate prepared quota.val⟩ ∈ made.entries := by
  rw [made.generated]
  exact List.mem_map.mpr ⟨quota,List.mem_finRange _,rfl⟩

theorem every_uniform_legal_fee_has_its_own_paid_candidate {source : SourceQuota.Generated prepared}
    {domain : SourceQuota.Catalogue source.snapshot} (made : Candidates source domain) (units : Nat)
    (legal : ∀ cell ∈ source.snapshot.cached,cell.2.Legal units) :
    ∃ quota : domain.Quota,quota.val = units ∧ ⟨quota,generate prepared quota.val⟩ ∈ made.entries := by
  obtain ⟨quota,_,same⟩ := domain.every_uniform_legal_fee_quantity_is_generated units legal
  exact ⟨quota,same,every_source_quota_has_its_own_paid_candidate made quota⟩

inductive DomainResult (prepared : Prepared input) where
  | empty (source : SourceQuota.Generated prepared) (absent : source.snapshot.cached = [])
  | blocked (source : SourceQuota.Generated prepared) (cell : SourceQuota.CachedCell prepared)
      (listed : cell ∈ source.snapshot.cached) (broken : cell.2.units.isSome = false)
  | ready (source : SourceQuota.Generated prepared) (domain : SourceQuota.Catalogue source.snapshot)
      (same : source.result = .domain domain) (made : Candidates source domain)

def generateAll (prepared : Prepared input) : DomainResult prepared :=
  let source := SourceQuota.generate prepared
  match same : source.result with
  | .empty absent => .empty source absent
  | .blocked cell listed broken => .blocked source cell listed broken
  | .domain domain => .ready source domain same (candidates source domain)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.CandidatePayment
