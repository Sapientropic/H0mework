import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Bound.Dispatch
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Work
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.PaidSelection
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

structure Funded (prepared : Prepared input) (units : Nat) where
  private mk ::
  funding : EscrowBudget.Funding prepared units
  generated : funding = EscrowBudget.reserve prepared units
  nonempty : prepared.saved ≠ []
  all_paid : ∀ index : Index prepared,(funding.resultAt index).funded
abbrev Funded.family {units : Nat} (made : Funded prepared units) := made.funding.installed

inductive Failure (prepared : Prepared input) (units : Nat) where
  | empty (absent : prepared.saved = [])
  | refused (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
      (index : Index prepared) (broken : ¬ (funding.resultAt index).funded)
inductive Attempt (prepared : Prepared input) (units : Nat) where
  | failed (why : Failure prepared units)
  | paid (made : Funded prepared units)
def pay (prepared : Prepared input) (units : Nat) : Attempt prepared units :=
  if absent : prepared.saved = [] then .failed (.empty absent) else
    let funding := EscrowBudget.reserve prepared units
    match Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared) with
    | .rejected index _ broken => .failed (.refused funding rfl index broken)
    | .accepted all => .paid ⟨funding,rfl,absent,fun index => all index (List.mem_finRange _)⟩

structure Available (prepared : Prepared input) where
  private mk ::
  source : SourceQuota.Generated prepared
  source_generated : source = SourceQuota.generate prepared
  catalogue : SourceQuota.Catalogue source.snapshot
  result : source.result = .domain catalogue
  pool : Comparison.Pool catalogue
  pool_generated : pool = Comparison.generate catalogue
inductive NoDomain {prepared : Prepared input} (source : SourceQuota.Generated prepared) where
  | empty (absent : source.snapshot.cached = [])
  | blocked (cell : SourceQuota.CachedCell prepared) (listed : cell ∈ source.snapshot.cached) (broken : cell.2.units.isSome = false)
inductive View (prepared : Prepared input) where
  | missing (source : SourceQuota.Generated prepared) (why : NoDomain source)
  | ready (made : Available prepared)
def acquire (prepared : Prepared input) : View prepared :=
  let source := SourceQuota.generate prepared
  match same : source.result with
  | .empty absent => .missing source (.empty absent)
  | .blocked cell listed broken => .missing source (.blocked cell listed broken)
  | .domain catalogue => .ready ⟨source,rfl,catalogue,same,Comparison.generate catalogue,rfl⟩

structure Offer (prepared : Prepared input) where
  private mk ::
  dispatch : Funded prepared PaidDispatch.units
  initial : Available dispatch.family
  forecast : PaidDispatch.Programme initial.pool (Work.workBudget initial.pool)
  forecast_generated : forecast = PaidDispatch.generate initial.pool
  execution : Funded dispatch.family forecast.run.value

structure Release (prepared : Prepared input) where
  private mk ::
  offer : Offer prepared
  actual : Available offer.execution.family
  budget : PaidDispatch.Programme actual.pool (Work.workBudget actual.pool)
  budget_generated : budget = PaidDispatch.generate actual.pool
  covered : budget.run.value ≤ offer.forecast.run.value
  work : Work.Generated actual.pool
  work_generated : work = Work.generate actual.pool

inductive Outcome (prepared : Prepared input) where
  | unfunded (why : Failure prepared PaidDispatch.units)
  | initialUnavailable (dispatch : Funded prepared PaidDispatch.units)
      (source : SourceQuota.Generated dispatch.family) (why : NoDomain source)
  | executionUnfunded (dispatch : Funded prepared PaidDispatch.units) (initial : Available dispatch.family)
      (forecast : PaidDispatch.Programme initial.pool (Work.workBudget initial.pool))
      (generated : forecast = PaidDispatch.generate initial.pool) (why : Failure dispatch.family forecast.run.value)
  | actualUnavailable (offer : Offer prepared) (source : SourceQuota.Generated offer.execution.family) (why : NoDomain source)
  | shortfall (offer : Offer prepared) (actual : Available offer.execution.family)
      (budget : PaidDispatch.Programme actual.pool (Work.workBudget actual.pool))
      (generated : budget = PaidDispatch.generate actual.pool) (lacks : offer.forecast.run.value < budget.run.value)
  | released (made : Release prepared)

def compile (prepared : Prepared input) : Outcome prepared :=
  match pay prepared PaidDispatch.units with
  | .failed why => .unfunded why
  | .paid dispatch => match acquire dispatch.family with
    | .missing source why => .initialUnavailable dispatch source why
    | .ready initial =>
      let forecast := PaidDispatch.generate initial.pool
      match pay dispatch.family forecast.run.value with
      | .failed why => .executionUnfunded dispatch initial forecast rfl why
      | .paid execution =>
        let offer : Offer prepared := ⟨dispatch,initial,forecast,rfl,execution⟩
        match acquire execution.family with
        | .missing source why => .actualUnavailable offer source why
        | .ready actual =>
          let budget := PaidDispatch.generate actual.pool
          if covered : budget.run.value ≤ forecast.run.value then
            .released ⟨offer,actual,budget,rfl,covered,Work.generate actual.pool,rfl⟩
          else .shortfall offer actual budget rfl (Nat.lt_of_not_ge covered)

private theorem complete_work_bound {snapshot : SourceQuota.Snapshot prepared} {catalogue : SourceQuota.Catalogue snapshot}
    {pool : Comparison.Pool catalogue} (made : Work.Generated pool) : made.work.length ≤ Work.workBudget pool := by
  rcases made with ⟨compilation,compiled,receipt,reviewed⟩
  subst compilation
  exact Work.receipt_work_fits_the_source_budget pool (sections pool) (List.Perm.refl _) receipt

namespace Release
variable (released : Release prepared)
theorem complete_selection_and_replay_fit_the_actual_execution_fee :
    released.work.work.length ≤ released.offer.forecast.run.value := by
  have bounded := complete_work_bound released.work
  have original := released.budget.run.exact
  have paid := released.covered
  omega

def executionSlot (index : Index released.offer.dispatch.family) (ordinal : Fin released.work.work.length) :
    Fin (((released.offer.execution.funding.resultAt index).invoice (released.offer.execution.all_paid index)).bill.units) :=
  ⟨ordinal.val,by
    rw [((released.offer.execution.funding.resultAt index).invoice (released.offer.execution.all_paid index)).size]
    exact Nat.lt_of_lt_of_le ordinal.isLt released.complete_selection_and_replay_fit_the_actual_execution_fee⟩

theorem execution_slots_are_not_reused (index : Index released.offer.dispatch.family) :
    Function.Injective (released.executionSlot index) := by
  intro first second same
  exact Fin.ext (congrArg (fun slot => slot.val) same)

structure ExecutionAllocation (index : Index released.offer.dispatch.family) (ordinal : Fin released.work.work.length) where
  private mk ::
  invoice : EscrowBudget.Charge.Invoice (released.offer.execution.funding.resultAt index)
  slot : Fin invoice.bill.units
  event : Work.Operation released.actual.pool
  slot_exact : slot.val = ordinal.val
  event_exact : event = released.work.work[ordinal]

def executionAllocation (index : Index released.offer.dispatch.family) (ordinal : Fin released.work.work.length) :
    ExecutionAllocation released index ordinal :=
  ⟨(released.offer.execution.funding.resultAt index).invoice (released.offer.execution.all_paid index),
    released.executionSlot index ordinal,released.work.work[ordinal],rfl,rfl⟩

theorem every_event_reads_the_actual_paid_invoice (index : Index released.offer.dispatch.family) (ordinal : Fin released.work.work.length) :
    (released.executionAllocation index ordinal).invoice.bill.payment.succeeded = true ∧
    (released.executionAllocation index ordinal).invoice.bill.units = released.offer.forecast.run.value :=
  ⟨(released.executionAllocation index ordinal).invoice.paid,(released.executionAllocation index ordinal).invoice.size⟩

def dispatchSlot (index : Index prepared) (token : PaidDispatch.Token) :
    Fin (((released.offer.dispatch.funding.resultAt index).invoice (released.offer.dispatch.all_paid index)).bill.units) :=
  ⟨(PaidDispatch.ordinal token).val,by
    rw [((released.offer.dispatch.funding.resultAt index).invoice (released.offer.dispatch.all_paid index)).size]
    exact (PaidDispatch.ordinal token).isLt⟩

theorem the_two_budget_phases_cannot_reuse_dispatch_credit (index : Index prepared) :
    Function.Injective (released.dispatchSlot index) := by
  intro first second same
  apply PaidDispatch.ordinal_injective
  exact Fin.ext (congrArg (fun slot => slot.val) same)

def dispatchInstruction (token : PaidDispatch.Token) : PaidDispatch.Instruction :=
  match token.1 with
  | .initial => released.offer.forecast.trace.get ⟨token.2.val,by
      rw [released.offer.forecast_generated,PaidDispatch.generated_dispatch_is_the_fixed_source_program];exact token.2.isLt⟩
  | .actual => released.budget.trace.get ⟨token.2.val,by
      rw [released.budget_generated,PaidDispatch.generated_dispatch_is_the_fixed_source_program];exact token.2.isLt⟩

theorem dispatch_reads_the_actual_cached_phase_instruction (token : PaidDispatch.Token) :
    released.dispatchInstruction token = PaidDispatch.code[token.2] := by
  cases token with
  | mk phase slot =>
    cases phase with
    | initial =>
      dsimp only [dispatchInstruction]
      have trace := congrArg (fun p : PaidDispatch.Programme released.offer.initial.pool (Work.workBudget released.offer.initial.pool) => p.trace)
        released.offer.forecast_generated
      rw [PaidDispatch.generated_dispatch_is_the_fixed_source_program] at trace
      have observed := congrArg (fun xs : List PaidDispatch.Instruction => xs[slot.val]?) trace
      rw [List.getElem?_eq_getElem slot.isLt] at observed
      obtain ⟨_,same⟩ := List.getElem?_eq_some_iff.mp observed
      exact same
    | actual =>
      dsimp only [dispatchInstruction]
      have trace := congrArg (fun p : PaidDispatch.Programme released.actual.pool (Work.workBudget released.actual.pool) => p.trace)
        released.budget_generated
      rw [PaidDispatch.generated_dispatch_is_the_fixed_source_program] at trace
      have observed := congrArg (fun xs : List PaidDispatch.Instruction => xs[slot.val]?) trace
      rw [List.getElem?_eq_getElem slot.isLt] at observed
      obtain ⟨_,same⟩ := List.getElem?_eq_some_iff.mp observed
      exact same


theorem both_payments_preserve_every_original_point_order_and_multiplicity :
    released.offer.execution.family.saved.map Cell.point = prepared.saved.map Cell.point :=
  released.offer.execution.funding.source_order_and_multiplicity.trans released.offer.dispatch.funding.source_order_and_multiplicity

def unusedExecutionUnits := released.offer.forecast.run.value-released.work.work.length
theorem every_execution_unit_is_consumed_or_retained :
    released.work.work.length+released.unusedExecutionUnits = released.offer.forecast.run.value := by
  have bounded := released.complete_selection_and_replay_fit_the_actual_execution_fee
  unfold unusedExecutionUnits
  omega
end Release

inductive Debt where
  | original (family : Prepared input) (debt : Policy.Obligation family)
  | fee {family : Prepared input} {units : Nat} (entry : EscrowBudget.CachedCharge family units)
  | source {family : Prepared input} (debt : SourceQuota.Debt family)
  | pool {family : Prepared input} {snapshot : SourceQuota.Snapshot family} {catalogue : SourceQuota.Catalogue snapshot}
      (pool : Comparison.Pool catalogue) (debt : Comparison.Pool.Debt pool)
  | budget {family : Prepared input} {snapshot : SourceQuota.Snapshot family} {catalogue : SourceQuota.Catalogue snapshot}
      (pool : Comparison.Pool catalogue) (event : Bound.Event pool)
  | selection {family : Prepared input} {snapshot : SourceQuota.Snapshot family} {catalogue : SourceQuota.Catalogue snapshot}
      (pool : Comparison.Pool catalogue) (work : Work.Generated pool) (debt : Work.Generated.Debt work)
  | quoteInternals
  | sourceAdmission
  | budgetBody
  | primitiveInternals
  | ledgerInstallation
  | storage
  | announcement

def originalDebts (family : Prepared input) : List (Debt (input := input)) := (Policy.obligations family).map (.original family)
def fundingDebts {units : Nat} (funding : EscrowBudget.Funding prepared units) : List (Debt (input := input)) :=
  originalDebts prepared ++ funding.cached.map Debt.fee

def Failure.pending {units : Nat} : Failure prepared units → List (Debt (input := input))
  | .empty _ => originalDebts prepared
  | .refused funding .. => fundingDebts funding

def Available.pending (made : Available prepared) : List (Debt (input := input)) :=
  made.source.pending.map Debt.source ++ made.pool.pending.map (Debt.pool made.pool)

def Offer.pending (made : Offer prepared) : List (Debt (input := input)) :=
  fundingDebts made.dispatch.funding ++ made.initial.pending ++ made.forecast.run.work.map (Debt.budget made.initial.pool) ++ fundingDebts made.execution.funding

def Outcome.pending : Outcome prepared → List (Debt (input := input))
  | .unfunded why => why.pending
  | .initialUnavailable dispatch source _ => fundingDebts dispatch.funding ++ source.pending.map Debt.source
  | .executionUnfunded dispatch initial forecast _ why => fundingDebts dispatch.funding ++ initial.pending ++
      forecast.run.work.map (Debt.budget initial.pool) ++ why.pending
  | .actualUnavailable offer source _ => offer.pending ++ source.pending.map Debt.source
  | .shortfall offer actual budget .. => offer.pending ++ actual.pending ++ budget.run.work.map (Debt.budget actual.pool)
  | .released made => made.offer.pending ++ made.actual.pending ++ made.budget.run.work.map (Debt.budget made.actual.pool) ++
      made.work.debts.map (Debt.selection made.actual.pool made.work)

structure Record (prepared : Prepared input) where
  private mk ::
  outcome : Outcome prepared
  generated : outcome = compile prepared

def generate (prepared : Prepared input) : Record prepared := ⟨compile prepared,rfl⟩
def Record.pending (made : Record prepared) : List (Debt (input := input)) := originalDebts prepared ++ made.outcome.pending ++
  [.quoteInternals,.sourceAdmission,.budgetBody,.primitiveInternals,.ledgerInstallation,.storage,.announcement]
theorem every_original_debt_is_retained (made : Record prepared) (debt : Policy.Obligation prepared)
    (inside : debt ∈ Policy.obligations prepared) : Debt.original prepared debt ∈ made.pending :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨debt,inside,rfl⟩))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.PaidSelection

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.PaidSelection
namespace PaymentAcquisition
set_option backward.isDefEq.respectTransparency false
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

variable {units : Nat}
abbrev Check (funding : EscrowBudget.Funding prepared units) (remaining : List (Index prepared)) :=
  Distributed.Inspection (fun index : Index prepared => (funding.resultAt index).funded) remaining
private def liftCheck (funding : EscrowBudget.Funding prepared units) (head : Index prepared)
    {tail : List (Index prepared)} (checked : (funding.resultAt head).funded) : Check funding tail → Check funding (head::tail)
  | .accepted all => .accepted (by
      intro index inside;rcases List.mem_cons.mp inside with same | later
      · subst index;exact checked
      · exact all index later)
  | .rejected index listed broken => .rejected index (List.mem_cons_of_mem _ listed) broken
private theorem liftCheck_exact (funding : EscrowBudget.Funding prepared units) (head : Index prepared)
    (tail : List (Index prepared)) (checked : (funding.resultAt head).funded) :
    liftCheck funding head checked (Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) tail) =
      Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (head::tail) := by
  simp only [Distributed.inspect,checked,↓reduceDIte]
  cases Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) tail <;> rfl
private def fromCheck (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
    (nonempty : prepared.saved ≠ []) : Check funding (keys prepared) → Attempt prepared units
  | .rejected index _ broken => .failed (.refused funding generated index broken)
  | .accepted all => .paid ⟨funding,generated,nonempty,fun index => all index (List.mem_finRange _)⟩
private theorem fromCheck_exact (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
    (nonempty : prepared.saved ≠ []) (checked : Check funding (keys prepared))
    (actual : checked = Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared)) :
    fromCheck funding generated nonempty checked = pay prepared units := by
  cases generated;cases actual
  simp only [pay,dif_neg nonempty]
  cases Distributed.inspect (fun index : Index prepared => ((EscrowBudget.reserve prepared units).resultAt index).funded) (keys prepared) <;> rfl
inductive State (prepared : Prepared input) (units : Nat) where
  | opening
  | funding (nonempty : prepared.saved ≠ []) (cursor : EscrowBudget.Acquisition.State prepared units)
  | checking (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
      (nonempty : prepared.saved ≠ []) (remaining : List (Index prepared))
      (embed : Check funding remaining → Check funding (keys prepared))
      (coherent : embed (Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) remaining) =
        Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared))
  | finished (attempt : Attempt prepared units) (generated : attempt = pay prepared units)
def initial (prepared : Prepared input) (units : Nat) : State prepared units := .opening
inductive Event (prepared : Prepared input) (units : Nat) where
  | opened
  | funding (event : EscrowBudget.Acquisition.Event prepared units)
  | funded (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
  | checked (funding : EscrowBudget.Funding prepared units) (index : Index prepared) (value : Bool)
      (actual : value = decide (funding.resultAt index).funded)
  | completed (attempt : Attempt prepared units) (generated : attempt = pay prepared units)
private def finishCheck (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
    (nonempty : prepared.saved ≠ []) (checked : Check funding (keys prepared))
    (actual : checked = Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared)) : State prepared units :=
  .finished (fromCheck funding generated nonempty checked) (fromCheck_exact funding generated nonempty checked actual)
def move : State prepared units → Option (State prepared units × Event prepared units)
  | .opening => if absent : prepared.saved = [] then
      some (.finished (.failed (.empty absent)) (by simp only [pay,dif_pos absent]),.opened)
    else some (.funding absent (EscrowBudget.Acquisition.initial prepared units),.opened)
  | .funding nonempty (.finished funding generated) =>
      some (.checking funding generated nonempty (keys prepared) id rfl,.funded funding generated)
  | .funding nonempty cursor@(.reading ..) => match _step : EscrowBudget.Acquisition.move cursor with
      | none => none
      | some (after,event) => some (.funding nonempty after,.funding event)
  | .checking funding generated nonempty [] embed coherent =>
      let attempt := fromCheck funding generated nonempty (embed (.accepted (by simp)))
      let exact := fromCheck_exact funding generated nonempty _ coherent
      some (.finished attempt exact,.completed attempt exact)
  | .checking funding generated nonempty (head::tail) embed coherent =>
      if checked : (funding.resultAt head).funded then
        some (.checking funding generated nonempty tail (fun later => embed (liftCheck funding head checked later))
          (by rw [liftCheck_exact];exact coherent),.checked funding head true (by simp [checked]))
      else some (finishCheck funding generated nonempty (embed (.rejected head List.mem_cons_self checked)) (by
          rw [←coherent];congr 1;rw [Distributed.inspect,dif_neg checked]),.checked funding head false (by simp [checked]))
  | .finished .. => none
def State.rank : State prepared units → Nat
  | .opening => 2*(keys prepared).length+4
  | .funding _ cursor => cursor.rank+(keys prepared).length+2
  | .checking _ _ _ remaining .. => remaining.length+1
  | .finished .. => 0
def State.done : State prepared units → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared units} {event : Event prepared units}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | opening =>
      dsimp only [move] at actual;split at actual
      all_goals cases Option.some.inj actual;simp only [State.rank,EscrowBudget.Acquisition.initial,EscrowBudget.Acquisition.State.rank];omega
  | funding nonempty cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,EscrowBudget.Acquisition.State.rank];omega
      | reading =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step;cases Option.some.inj actual
            have less := EscrowBudget.Acquisition.progress step;simp only [State.rank];omega
  | checking funding generated nonempty remaining embed coherent =>
      cases remaining with
      | nil => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,List.length_nil];omega
      | cons head tail =>
          dsimp only [move] at actual;split at actual
          all_goals cases Option.some.inj actual;simp only [State.rank,finishCheck,List.length_cons];omega
  | finished => cases actual
theorem no_move_iff_done (before : State prepared units) : move before = none ↔ before.done = true := by
  cases before with
  | opening => dsimp only [move,State.done];split <;> simp
  | funding nonempty cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | reading cached remaining conserved =>
          dsimp only [move,State.done];split
          · rename_i stopped
            cases remaining <;> simp [EscrowBudget.Acquisition.move] at stopped
          · simp
  | checking funding generated nonempty remaining embed coherent =>
      cases remaining <;> dsimp only [move,State.done] <;> first | (split <;> simp) | simp
  | finished => simp [move,State.done]
end PaymentAcquisition

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.PaidSelection

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.PaidSelection
namespace SourceAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

set_option backward.isDefEq.respectTransparency false
private theorem empty_exact (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
    (absent : source.snapshot.cached = []) (result : source.result = .empty absent) :
    View.missing source (.empty absent) = acquire prepared := by
  cases generated;dsimp only [acquire];split
  · rfl
  · rename_i cell listed broken observed;cases result.symm.trans observed
  · rename_i catalogue observed;cases result.symm.trans observed
private theorem blocked_exact (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
    (cell : SourceQuota.CachedCell prepared) (listed : cell ∈ source.snapshot.cached) (broken : cell.2.units.isSome = false)
    (result : source.result = .blocked cell listed broken) :
    View.missing source (.blocked cell listed broken) = acquire prepared := by
  cases generated;dsimp only [acquire];split
  · rename_i absent observed;cases result.symm.trans observed
  · rename_i other inside failure observed;cases SourceQuota.Result.blocked.inj (result.symm.trans observed);rfl
  · rename_i catalogue observed;cases result.symm.trans observed
private theorem ready_exact (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
    (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue)
    (pool : SourceQuota.Comparison.Pool catalogue) (actual : pool = SourceQuota.Comparison.generate catalogue) :
    View.ready (⟨source,generated,catalogue,result,pool,actual⟩ : Available prepared) = acquire prepared := by
  cases generated;cases actual;dsimp only [acquire];split
  · rename_i absent observed;cases result.symm.trans observed
  · rename_i cell listed broken observed;cases result.symm.trans observed
  · rename_i other observed;cases SourceQuota.Result.domain.inj (result.symm.trans observed);rfl

def sourceTail (prepared : Prepared input) :=
  let source := SourceQuota.generate prepared
  match source.result with | .domain catalogue => SourceQuota.Comparison.OfferAcquisition.remainingWeight catalogue catalogue.quotas+2 | _ => 0
private theorem sourceTail_domain (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
    (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue) :
    sourceTail prepared = SourceQuota.Comparison.OfferAcquisition.remainingWeight catalogue catalogue.quotas+2 := by
  cases generated;dsimp only [sourceTail];rw [result]
inductive State (prepared : Prepared input) where
  | source (cursor : SourceQuota.Acquisition.State prepared)
  | pool (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue)
      (cursor : SourceQuota.Comparison.OfferAcquisition.State catalogue)
  | finished (view : View prepared) (generated : view = acquire prepared)
def initial (prepared : Prepared input) : State prepared := .source (SourceQuota.Acquisition.initial prepared)
inductive Event (prepared : Prepared input) where
  | source (event : SourceQuota.Acquisition.Event prepared)
  | captured (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
  | pool (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot)
      (event : SourceQuota.Comparison.OfferAcquisition.Event catalogue)
  | completed (view : View prepared) (generated : view = acquire prepared)
def move : State prepared → Option (State prepared × Event prepared)
  | .source (.finished (.unavailable source generated outside)) => match result : source.result with
    | .empty absent =>
        let view := View.missing source (.empty absent)
        let exact := empty_exact source generated absent result
        some (.finished view exact,.completed view exact)
    | .blocked cell listed broken =>
        let view := View.missing source (.blocked cell listed broken)
        let exact := blocked_exact source generated cell listed broken result
        some (.finished view exact,.completed view exact)
    | .domain catalogue => False.elim (by rw [result] at outside;exact outside)
  | .source (.finished (.domain source generated catalogue result limit bound)) =>
      some (.pool source generated catalogue result (SourceQuota.Comparison.OfferAcquisition.initial catalogue limit bound),.captured source generated)
  | .source cursor@(.observing ..) | .source cursor@(.validating ..) | .source cursor@(.seeding ..)
  | .source cursor@(.folding ..) | .source cursor@(.reducing ..) => match _step : SourceQuota.Acquisition.move cursor with
    | none => none
    | some (after,event) => some (.source after,.source event)
  | .pool source generated catalogue result (.finished pool actual) =>
      let made : Available prepared := ⟨source,generated,catalogue,result,pool,actual⟩
      let exact := ready_exact source generated catalogue result pool actual
      some (.finished (.ready made) exact,.completed (.ready made) exact)
  | .pool source generated catalogue result cursor@(.reading ..)
  | .pool source generated catalogue result cursor@(.working ..) => match _step : SourceQuota.Comparison.OfferAcquisition.move cursor with
    | none => none
    | some (after,event) => some (.pool source generated catalogue result after,.pool source catalogue event)
  | .finished .. => none
def State.rank : State prepared → Nat
  | .source cursor => cursor.rank+sourceTail prepared+1
  | .pool _ _ _ _ cursor => cursor.rank+1
  | .finished .. => 0
def State.done : State prepared → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared} {event : Event prepared}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | source cursor =>
      cases cursor with
      | finished output =>
          cases output with
          | unavailable source generated outside =>
              dsimp only [move] at actual;split at actual
              · cases Option.some.inj actual;simp only [State.rank,SourceQuota.Acquisition.State.rank];omega
              · cases Option.some.inj actual;simp only [State.rank,SourceQuota.Acquisition.State.rank];omega
              · rename_i catalogue result;rw [result] at outside;exact False.elim outside
          | domain source generated catalogue result limit bound =>
              dsimp only [move] at actual;cases Option.some.inj actual
              simp only [State.rank,SourceQuota.Acquisition.State.rank,SourceQuota.Comparison.OfferAcquisition.initial_rank,sourceTail_domain source generated catalogue result];omega
      | observing | validating | seeding | folding | reducing =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := SourceQuota.Acquisition.each_actual_step_decreases_source_rank step
               simp only [State.rank];omega)
  | pool source generated catalogue result cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,SourceQuota.Comparison.OfferAcquisition.State.rank];omega
      | reading | working =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step;cases Option.some.inj actual
            have less := SourceQuota.Comparison.OfferAcquisition.progress step;simp only [State.rank];omega
  | finished => cases actual
theorem no_move_iff_done (before : State prepared) : move before = none ↔ before.done = true := by
  cases before with
  | source cursor =>
      cases cursor with
      | finished output =>
          cases output with
          | domain => simp [move,State.done]
          | unavailable source generated outside =>
              dsimp only [move,State.done];split
              · simp
              · simp
              · rename_i catalogue result;rw [result] at outside;exact False.elim outside
      | observing | validating | seeding | folding | reducing =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (SourceQuota.Acquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | pool source generated catalogue result cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | reading | working =>
          dsimp only [move,State.done];split
          · rename_i stopped;have done := (SourceQuota.Comparison.OfferAcquisition.no_move_iff_done _).mp stopped;cases done
          · simp
  | finished => simp [move,State.done]
end SourceAcquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.PaidSelection
