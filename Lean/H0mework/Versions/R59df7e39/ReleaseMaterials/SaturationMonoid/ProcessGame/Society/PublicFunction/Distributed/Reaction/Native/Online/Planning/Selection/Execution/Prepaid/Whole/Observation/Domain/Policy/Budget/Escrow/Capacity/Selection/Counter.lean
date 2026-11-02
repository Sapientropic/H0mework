import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Machine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}

structure Programme (prepared : Prepared input) (units : Nat) where
  private mk ::
  paid : PaidSelection.Funded prepared units
  actual : PaidSelection.Available paid.family
  calculation : Calculation actual.pool units
  generated : calculation = calculate actual.pool units

structure Release (prepared : Prepared input) (units : Nat) where
  private mk ::
  programme : Programme prepared units
  value : Nat
  completed : programme.calculation.run.endpoint = .program [value] []
  correct : value = Body.units programme.actual.pool + Work.workBudget programme.actual.pool
  covered : programme.calculation.run.spent + value ≤ units
  body : Body.Generated programme.actual.pool
  body_generated : body = Body.generate programme.actual.pool
  work : Work.Generated programme.actual.pool
  work_generated : work = Work.generate programme.actual.pool

inductive Outcome (prepared : Prepared input) (units : Nat) where
  | unfunded (why : PaidSelection.Failure prepared units)
  | unavailable (paid : PaidSelection.Funded prepared units)
      (source : SourceQuota.Generated paid.family) (why : PaidSelection.NoDomain source)
  | exhausted (made : Programme prepared units) (state : Frame made.actual.pool)
      (residual : made.calculation.run.endpoint = state) (all_spent : made.calculation.run.spent = units)
  | shortfall (made : Programme prepared units) (value : Nat)
      (completed : made.calculation.run.endpoint = .program [value] [])
      (correct : value = Body.units made.actual.pool + Work.workBudget made.actual.pool)
      (lacks : units < made.calculation.run.spent + value)
  | released (made : Release prepared units)

def finish (made : Programme prepared units) : Outcome prepared units :=
  match made.calculation.result with
  | .exhausted state residual all_spent => .exhausted made state residual all_spent
  | .budget value completed correct =>
    if covered : made.calculation.run.spent + value ≤ units then
      .released ⟨made,value,completed,correct,covered,Body.generate made.actual.pool,rfl,Work.generate made.actual.pool,rfl⟩
    else .shortfall made value completed correct (Nat.lt_of_not_ge covered)

def generate (prepared : Prepared input) (units : Nat) : Outcome prepared units :=
  match PaidSelection.pay prepared units with
  | .failed why => .unfunded why
  | .paid paid => match PaidSelection.acquire paid.family with
    | .missing source why => .unavailable paid source why
    | .ready actual => finish ⟨paid,actual,calculate actual.pool units,rfl⟩

namespace Release
variable (made : Release prepared units)
theorem body_fits : made.body.budget.work.length ≤ Body.units made.programme.actual.pool := by
  rw [made.body_generated];exact Body.generated_body_fits_the_source_units _
theorem selection_fits : made.work.work.length ≤ Work.workBudget made.programme.actual.pool := by
  rw [made.work_generated]
  exact Work.receipt_work_fits_the_source_budget made.programme.actual.pool (sections made.programme.actual.pool)
    (List.Perm.refl _) (Work.generate made.programme.actual.pool).receipt

theorem counter_body_and_full_selection_fit_the_actual_invoice :
    made.programme.calculation.run.spent + made.body.budget.work.length + made.work.work.length ≤ units := by
  have := made.body_fits;have := made.selection_fits;have := made.covered;have := made.correct;omega

abbrev CounterOrdinal := Fin made.programme.calculation.run.work.length
abbrev BodyOrdinal := Fin made.body.budget.work.length
abbrev SelectionOrdinal := Fin made.work.work.length
abbrev Token := Sum made.CounterOrdinal (Sum made.BodyOrdinal made.SelectionOrdinal)
def ordinal : made.Token → Nat
  | .inl counter => counter.val
  | .inr (.inl body) => made.programme.calculation.run.spent+body.val
  | .inr (.inr selection) => made.programme.calculation.run.spent+Body.units made.programme.actual.pool+selection.val

theorem ordinal_bound (token : made.Token) : made.ordinal token < units := by
  have counter := made.programme.calculation.run.work_count
  have body := made.body_fits
  have selection := made.selection_fits
  have covered := made.covered
  have correct := made.correct
  cases token with
  | inl token => have := token.isLt;dsimp [ordinal];omega
  | inr token => cases token with
    | inl token => have := token.isLt;dsimp [ordinal];omega
    | inr token => have := token.isLt;dsimp [ordinal];omega

theorem ordinal_injective : Function.Injective made.ordinal := by
  intro first second same
  have counter := made.programme.calculation.run.work_count
  have body := made.body_fits
  cases first with
  | inl first => cases second with
    | inl second => exact congrArg Sum.inl (Fin.ext same)
    | inr second => cases second <;> have := first.isLt <;> dsimp [ordinal] at same <;> omega
  | inr first => cases first with
    | inl first => cases second with
      | inl second => have := second.isLt;dsimp [ordinal] at same;omega
      | inr second => cases second with
        | inl second => apply congrArg (fun x => Sum.inr (Sum.inl x));apply Fin.ext;dsimp [ordinal] at same;omega
        | inr second => have := first.isLt;dsimp [ordinal] at same;omega
    | inr first => cases second with
      | inl second => have := second.isLt;dsimp [ordinal] at same;omega
      | inr second => cases second with
        | inl second => have := second.isLt;dsimp [ordinal] at same;omega
        | inr second => apply congrArg (fun x => Sum.inr (Sum.inr x));apply Fin.ext;dsimp [ordinal] at same;omega

def slot (index : Index prepared) (token : made.Token) :
    Fin (((made.programme.paid.funding.resultAt index).invoice (made.programme.paid.all_paid index)).bill.units) :=
  ⟨made.ordinal token,by rw [((made.programme.paid.funding.resultAt index).invoice (made.programme.paid.all_paid index)).size];exact made.ordinal_bound token⟩
theorem all_three_work_families_have_disjoint_actual_invoice_slots (index : Index prepared) : Function.Injective (made.slot index) := by
  intro first second same
  exact made.ordinal_injective (congrArg (fun slot => slot.val) same)

inductive Event where
  | counter (event : Counter.Event made.programme.actual.pool)
  | body (event : Bound.Event made.programme.actual.pool)
  | selection (event : Work.Operation made.programme.actual.pool)
def event : made.Token → made.Event
  | .inl counter => .counter made.programme.calculation.run.work[counter]
  | .inr (.inl body) => .body made.body.budget.work[body]
  | .inr (.inr selection) => .selection made.work.work[selection]

structure Allocation (index : Index prepared) (token : made.Token) where
  private mk ::
  invoice : EscrowBudget.Charge.Invoice (made.programme.paid.funding.resultAt index)
  slot : Fin invoice.bill.units
  event : made.Event
  slot_exact : slot.val = made.ordinal token
  event_exact : event = made.event token

def allocation (index : Index prepared) (token : made.Token) : Allocation made index token :=
  ⟨(made.programme.paid.funding.resultAt index).invoice (made.programme.paid.all_paid index),made.slot index token,made.event token,rfl,rfl⟩
theorem every_event_reads_its_actual_paid_invoice (index : Index prepared) (token : made.Token) :
    (made.allocation index token).invoice.bill.payment.succeeded = true ∧
    (made.allocation index token).invoice.bill.units = units ∧
    (made.allocation index token).event = made.event token :=
  ⟨(made.allocation index token).invoice.paid,(made.allocation index token).invoice.size,rfl⟩

def unused := units-(made.programme.calculation.run.spent+made.body.budget.work.length+made.work.work.length)
theorem every_prepaid_credit_is_used_or_retained :
    made.programme.calculation.run.spent+made.body.budget.work.length+made.work.work.length+made.unused = units := by
  have := made.counter_body_and_full_selection_fit_the_actual_invoice
  unfold unused;omega
end Release

inductive Debt where
  | prior (debt : CandidatePayment.Debt (input := input))
  | counter {family : Prepared input} {snapshot : SourceQuota.Snapshot family} {catalogue : SourceQuota.Catalogue snapshot}
      (pool : Comparison.Pool catalogue) (event : Counter.Event pool)
  | residual (made : Programme prepared units)
  | expressionConstruction
  | operandInternals
  | guard
  | allocation

def Programme.pending (made : Programme prepared units) : List (Debt (prepared := prepared) (units := units)) :=
  (PaidSelection.fundingDebts made.paid.funding ++ made.actual.pending).map (fun debt => .prior (.prior debt)) ++
    made.calculation.run.work.map (.counter made.actual.pool) ++ [.residual made]
def Outcome.pending : Outcome prepared units → List (Debt (prepared := prepared) (units := units))
  | .unfunded why => why.pending.map (fun debt => .prior (.prior debt))
  | .unavailable paid source _ =>
      (PaidSelection.fundingDebts paid.funding ++ source.pending.map PaidSelection.Debt.source).map (fun debt => .prior (.prior debt))
  | .exhausted made .. | .shortfall made .. => made.pending
  | .released made => made.programme.pending ++
      (made.body.budget.work.map (PaidSelection.Debt.budget made.programme.actual.pool) ++
        made.work.debts.map (PaidSelection.Debt.selection made.programme.actual.pool made.work)).map (fun debt => .prior (.prior debt))

structure Record (prepared : Prepared input) (units : Nat) where
  private mk ::
  outcome : Outcome prepared units
  generated : outcome = generate prepared units
def record (prepared : Prepared input) (units : Nat) : Record prepared units := ⟨generate prepared units,rfl⟩
def Record.pending (made : Record prepared units) : List (Debt (prepared := prepared) (units := units)) :=
  (PaidSelection.originalDebts prepared).map (fun debt => .prior (.prior debt)) ++ made.outcome.pending ++
  [.expressionConstruction,.operandInternals,.guard,.allocation,
    .prior .quoteInternals,.prior .sourceService,.prior .primitiveInternals,.prior .ledgerInstallation,.prior .storage,.prior .announcement]
theorem every_original_debt_survives (made : Record prepared units) (debt : Policy.Obligation prepared)
    (inside : debt ∈ Policy.obligations prepared) : Debt.prior (.prior (.original prepared debt)) ∈ made.pending := by
  apply List.mem_append_left;apply List.mem_append_left
  exact List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨debt,inside,rfl⟩,rfl⟩

structure Candidates {prepared : Prepared input} (source : SourceQuota.Generated prepared) (domain : SourceQuota.Catalogue source.snapshot) where
  private mk ::
  entries : List ((quota : domain.Quota) × Record prepared quota.val)
  generated : entries = domain.quotas.map (fun quota => ⟨quota,record prepared quota.val⟩)
def candidates {prepared : Prepared input} (source : SourceQuota.Generated prepared) (domain : SourceQuota.Catalogue source.snapshot) : Candidates source domain :=
  ⟨domain.quotas.map (fun quota => ⟨quota,record prepared quota.val⟩),rfl⟩
theorem every_source_quota_is_retained {source : SourceQuota.Generated prepared} {domain : SourceQuota.Catalogue source.snapshot}
    (made : Candidates source domain) (quota : domain.Quota) : ⟨quota,record prepared quota.val⟩ ∈ made.entries := by
  rw [made.generated];exact List.mem_map.mpr ⟨quota,List.mem_finRange _,rfl⟩
theorem every_uniform_legal_fee_is_retained {source : SourceQuota.Generated prepared} {domain : SourceQuota.Catalogue source.snapshot}
    (made : Candidates source domain) (count : Nat) (legal : ∀ cell ∈ source.snapshot.cached,cell.2.Legal count) :
    ∃ quota : domain.Quota,quota.val = count ∧ ⟨quota,record prepared quota.val⟩ ∈ made.entries := by
  obtain ⟨quota,_,same⟩ := domain.every_uniform_legal_fee_quantity_is_generated count legal
  exact ⟨quota,same,every_source_quota_is_retained made quota⟩

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

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid
namespace RecordAcquisition
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}
private def packRecord (outcome : Outcome prepared units) (generated : outcome = generate prepared units) : Record prepared units := ⟨outcome,generated⟩
private theorem canonical (made : Record prepared units) : made = record prepared units := by
  rcases made with ⟨outcome,generated⟩;cases generated;rfl
private theorem programme_exact (paid : PaidSelection.Funded prepared units) (paid_exact : PaidSelection.pay prepared units = .paid paid)
    (actual : PaidSelection.Available paid.family) (acquired : PaidSelection.acquire paid.family = .ready actual)
    (calculation : Calculation actual.pool units) (generated : calculation = calculate actual.pool units) :
    finish (⟨paid,actual,calculation,generated⟩ : Programme prepared units) = generate prepared units := by
  cases generated
  simp only [generate,paid_exact,acquired]

inductive State (prepared : Prepared input) (units : Nat) where
  | paying
  | acquiring (paid : PaidSelection.Funded prepared units) (generated : PaidSelection.pay prepared units = .paid paid)
  | calculating (paid : PaidSelection.Funded prepared units) (generated : PaidSelection.pay prepared units = .paid paid)
      (actual : PaidSelection.Available paid.family) (acquired : PaidSelection.acquire paid.family = .ready actual)
      (cursor : Counter.Acquisition.State actual.pool units)
  | finishing (made : Programme prepared units) (generated : finish made = generate prepared units)
  | body (made : Programme prepared units) (generated : finish made = generate prepared units)
      (value : Nat) (completed : made.calculation.run.endpoint = .program [value] [])
      (correct : value = Body.units made.actual.pool + Work.workBudget made.actual.pool)
      (result : made.calculation.result = .budget value completed correct)
      (covered : made.calculation.run.spent+value ≤ units)
  | work (made : Programme prepared units) (generated : finish made = generate prepared units)
      (value : Nat) (completed : made.calculation.run.endpoint = .program [value] [])
      (correct : value = Body.units made.actual.pool + Work.workBudget made.actual.pool)
      (result : made.calculation.result = .budget value completed correct)
      (covered : made.calculation.run.spent+value ≤ units)
      (body : Body.Generated made.actual.pool) (body_generated : body = Body.generate made.actual.pool)
  | sealing (outcome : Outcome prepared units) (generated : outcome = generate prepared units)
  | finished (made : Record prepared units) (generated : made = record prepared units)
inductive Event (prepared : Prepared input) (units : Nat) where
  | payment (attempt : PaidSelection.Attempt prepared units) (actual : attempt = PaidSelection.pay prepared units)
  | source (paid : PaidSelection.Funded prepared units) (view : PaidSelection.View paid.family) (actual : view = PaidSelection.acquire paid.family)
  | counter (paid : PaidSelection.Funded prepared units) (actual : PaidSelection.Available paid.family)
      (event : Counter.Acquisition.Event actual.pool units)
  | counted (made : Programme prepared units)
  | disposition (outcome : Outcome prepared units)
  | body (made : Programme prepared units) (body : Body.Generated made.actual.pool) (generated : body = Body.generate made.actual.pool)
  | selection (made : Programme prepared units) (work : Work.Generated made.actual.pool) (generated : work = Work.generate made.actual.pool)
  | cached (made : Record prepared units) (generated : made = record prepared units)

def initial (prepared : Prepared input) (units : Nat) : State prepared units := .paying

def move : State prepared units → Option (State prepared units × Event prepared units)
  | .paying => match actual : PaidSelection.pay prepared units with
    | .failed why => some (.sealing (.unfunded why) (by simp only [generate,actual]),.payment (.failed why) actual.symm)
    | .paid paid => some (.acquiring paid actual,.payment (.paid paid) actual.symm)
  | .acquiring paid generated => match acquired : PaidSelection.acquire paid.family with
    | .missing source why => some (.sealing (.unavailable paid source why) (by simp only [generate,generated,acquired]),.source paid (.missing source why) acquired.symm)
    | .ready actual => some (.calculating paid generated actual acquired (Counter.Acquisition.initial actual.pool units),.source paid (.ready actual) acquired.symm)
  | .calculating paid generated actual acquired (.finished calculation calculated) =>
      let made : Programme prepared units := ⟨paid,actual,calculation,calculated⟩
      some (.finishing made (programme_exact paid generated actual acquired calculation calculated),.counted made)
  | .calculating paid generated actual acquired cursor@(.running ..) =>
      match _step : Counter.Acquisition.move actual.pool units cursor with
      | none => none
      | some (after,event) => some (.calculating paid generated actual acquired after,.counter paid actual event)
  | .finishing made generated => match result : made.calculation.result with
    | .exhausted state residual all_spent =>
        let outcome := Outcome.exhausted made state residual all_spent
        some (.sealing outcome (by simpa only [finish,result] using generated),.disposition outcome)
    | .budget value completed correct =>
        if covered : made.calculation.run.spent+value ≤ units then
          some (.body made generated value completed correct result covered,.counted made)
        else
          let outcome := Outcome.shortfall made value completed correct (Nat.lt_of_not_ge covered)
          some (.sealing outcome (by simpa only [finish,result,dif_neg covered] using generated),.disposition outcome)
  | .body made generated value completed correct result covered =>
      let body := Body.generate made.actual.pool
      some (.work made generated value completed correct result covered body rfl,.body made body rfl)
  | .work made generated value completed correct result covered body bodyGenerated =>
      let work := Work.generate made.actual.pool
      let release : Release prepared units := ⟨made,value,completed,correct,covered,body,bodyGenerated,work,rfl⟩
      some (.sealing (.released release) (by
        cases bodyGenerated
        simpa only [finish,result,dif_pos covered] using generated),.selection made work rfl)
  | .sealing outcome generated =>
      let made := packRecord outcome generated
      some (.finished made (canonical made),.cached made (canonical made))
  | .finished .. => none

def State.rank : State prepared units → Nat
  | .paying => units+9
  | .acquiring .. => units+8
  | .calculating _ _ _ _ cursor => cursor.rank _ units+6
  | .finishing .. => 5
  | .body .. => 4
  | .work .. => 3
  | .sealing .. => 1
  | .finished .. => 0
def State.done : State prepared units → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared units} {event : Event prepared units}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | paying =>
      dsimp only [move] at actual;split at actual
      all_goals cases Option.some.inj actual;simp only [State.rank];omega
  | acquiring =>
      dsimp only [move] at actual;split at actual
      all_goals cases Option.some.inj actual;simp only [State.rank,Counter.Acquisition.initial,Counter.Acquisition.State.rank];omega
  | calculating paid generated acquired sourceEq cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Counter.Acquisition.State.rank];omega
      | running =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step;cases Option.some.inj actual
            have less := Counter.Acquisition.progress acquired.pool units step
            simp only [State.rank];omega
  | finishing =>
      dsimp only [move] at actual;split at actual
      · cases Option.some.inj actual;simp only [State.rank];omega
      · split at actual
        all_goals cases Option.some.inj actual;simp only [State.rank];omega
  | body | work | sealing =>
      all_goals dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual

theorem no_move_iff_done (before : State prepared units) : move before = none ↔ before.done = true := by
  cases before with
  | paying | acquiring => dsimp only [move,State.done];split <;> simp
  | calculating paid generated actual acquired cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | running =>
          dsimp only [move,State.done];split
          · rename_i stopped;have done := (Counter.Acquisition.no_move_iff_done actual.pool units _).mp stopped;cases done
          · simp
  | finishing => dsimp only [move,State.done];split <;> first | (split <;> simp) | simp
  | body | work | sealing | finished => simp [move,State.done]
end RecordAcquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid
namespace MenuAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}
  {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
abbrev Entry (catalogue : SourceQuota.Catalogue source.snapshot) := Sigma fun quota : catalogue.Quota => Record prepared quota.val
private def quotaList (catalogue : SourceQuota.Catalogue source.snapshot) (limit : Nat) (bound : limit = catalogue.bound) : List catalogue.Quota :=
  (List.finRange (limit+1)).map fun quota => ⟨quota.val,by rw [←bound];exact quota.isLt⟩
private theorem quotaList_exact (catalogue : SourceQuota.Catalogue source.snapshot) (limit : Nat) (bound : limit = catalogue.bound) :
    quotaList catalogue limit bound = catalogue.quotas := by
  subst limit
  simp only [quotaList,SourceQuota.Catalogue.quotas]
  exact List.map_id _
private theorem candidates_canonical (made : Candidates source catalogue) : made = candidates source catalogue := by
  rcases made with ⟨entries,generated⟩;cases generated;rfl
private def packCandidates (cached : List (Entry catalogue))
    (generated : cached = catalogue.quotas.map (fun quota => ⟨quota,record prepared quota.val⟩)) : Candidates source catalogue := ⟨cached,generated⟩
private theorem empty_exact (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
    (absent : source.snapshot.cached = []) (result : source.result = .empty absent) :
    DomainResult.empty source absent = generateAll prepared := by
  cases generated
  dsimp only [generateAll]
  split
  · rfl
  · rename_i cell listed broken observed;cases result.symm.trans observed
  · rename_i catalogue observed;cases result.symm.trans observed
private theorem blocked_exact (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
    (cell : SourceQuota.CachedCell prepared) (listed : cell ∈ source.snapshot.cached) (broken : cell.2.units.isSome = false)
    (result : source.result = .blocked cell listed broken) :
    DomainResult.blocked source cell listed broken = generateAll prepared := by
  cases generated
  dsimp only [generateAll]
  split
  · rename_i absent observed;cases result.symm.trans observed
  · rename_i other inside failure observed
    cases SourceQuota.Result.blocked.inj (result.symm.trans observed)
    rfl
  · rename_i catalogue observed;cases result.symm.trans observed
private theorem ready_exact (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
    (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue)
    (made : Candidates source catalogue) (actual : made = candidates source catalogue) :
    DomainResult.ready source catalogue result made = generateAll prepared := by
  cases generated;cases actual
  dsimp only [generateAll]
  split
  · rename_i absent observed;cases result.symm.trans observed
  · rename_i cell listed broken observed;cases result.symm.trans observed
  · rename_i other observed
    cases SourceQuota.Result.domain.inj (result.symm.trans observed)
    rfl

def quotaWeight (quota : catalogue.Quota) := quota.val+12
def remainingWeight (catalogue : SourceQuota.Catalogue source.snapshot) (remaining : List catalogue.Quota) := (remaining.map quotaWeight).sum
def sourceTail (prepared : Prepared input) :=
  let source := SourceQuota.generate prepared
  match source.result with
  | .domain catalogue => remainingWeight catalogue catalogue.quotas+4
  | _ => 0
private theorem sourceTail_domain (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
    (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue) :
    sourceTail prepared = remainingWeight catalogue catalogue.quotas+4 := by
  cases generated
  dsimp only [sourceTail]
  rw [result]

inductive State (prepared : Prepared input) where
  | source (cursor : SourceQuota.Acquisition.State prepared)
  | listing (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue) (limit : Nat) (bound : limit = catalogue.bound)
  | waiting (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue)
      (cached : List (Entry catalogue)) (remaining : List catalogue.Quota)
      (conserved : cached++remaining.map (fun quota => ⟨quota,record prepared quota.val⟩) = catalogue.quotas.map (fun quota => ⟨quota,record prepared quota.val⟩))
  | working (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue)
      (cached : List (Entry catalogue)) (quota : catalogue.Quota) (rest : List catalogue.Quota)
      (conserved : cached++(quota::rest).map (fun quota => ⟨quota,record prepared quota.val⟩) = catalogue.quotas.map (fun quota => ⟨quota,record prepared quota.val⟩))
      (cursor : RecordAcquisition.State prepared quota.val)
  | finished (menu : DomainResult prepared) (generated : menu = generateAll prepared)
def initial (prepared : Prepared input) : State prepared := .source (SourceQuota.Acquisition.initial prepared)
inductive Event (prepared : Prepared input) where
  | source (event : SourceQuota.Acquisition.Event prepared)
  | captured (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
  | enumerated (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot) (limit : Nat) (bound : limit = catalogue.bound)
  | opened (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot) (quota : catalogue.Quota)
  | record (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot) (quota : catalogue.Quota)
      (event : RecordAcquisition.Event prepared quota.val)
  | cached (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot) (quota : catalogue.Quota)
      (made : Record prepared quota.val) (generated : made = Paid.record prepared quota.val)
  | complete (menu : DomainResult prepared) (generated : menu = generateAll prepared)

def move : State prepared → Option (State prepared × Event prepared)
  | .source (.finished (.unavailable source generated outside)) => match result : source.result with
    | .empty absent => some (.finished (.empty source absent) (empty_exact source generated absent result),.captured source generated)
    | .blocked cell listed broken => some (.finished (.blocked source cell listed broken) (blocked_exact source generated cell listed broken result),.captured source generated)
    | .domain catalogue => False.elim (by rw [result] at outside;exact outside)
  | .source (.finished (.domain source generated catalogue result limit bound)) =>
      some (.listing source generated catalogue result limit bound,.captured source generated)
  | .source cursor@(.observing ..) | .source cursor@(.validating ..) | .source cursor@(.seeding ..)
  | .source cursor@(.folding ..) | .source cursor@(.reducing ..) => match _actual : SourceQuota.Acquisition.move cursor with
    | none => none
    | some (after,event) => some (.source after,.source event)
  | .listing source generated catalogue result limit bound =>
      some (.waiting source generated catalogue result [] (quotaList catalogue limit bound) (by
        rw [quotaList_exact];rfl),.enumerated source catalogue limit bound)
  | .waiting source generated catalogue result cached [] conserved =>
      let made := packCandidates cached (by simpa only [List.map_nil,List.append_nil] using conserved)
      let menu := DomainResult.ready source catalogue result made
      let exact := ready_exact source generated catalogue result made (candidates_canonical made)
      some (.finished menu exact,.complete menu exact)
  | .waiting source generated catalogue result cached (quota::rest) conserved =>
      some (.working source generated catalogue result cached quota rest conserved (RecordAcquisition.initial prepared quota.val),.opened source catalogue quota)
  | .working source generated catalogue result cached quota rest conserved (.finished made actual) =>
      some (.waiting source generated catalogue result (cached++[⟨quota,made⟩]) rest (by
        simpa only [actual,List.map_cons,List.append_assoc,List.singleton_append] using conserved),.cached source catalogue quota made actual)
  | .working source generated catalogue result cached quota rest conserved cursor@(.paying)
  | .working source generated catalogue result cached quota rest conserved cursor@(.acquiring ..)
  | .working source generated catalogue result cached quota rest conserved cursor@(.calculating ..)
  | .working source generated catalogue result cached quota rest conserved cursor@(.finishing ..)
  | .working source generated catalogue result cached quota rest conserved cursor@(.body ..)
  | .working source generated catalogue result cached quota rest conserved cursor@(.work ..)
  | .working source generated catalogue result cached quota rest conserved cursor@(.sealing ..) =>
      match _actual : RecordAcquisition.move cursor with
      | none => none
      | some (after,event) => some (.working source generated catalogue result cached quota rest conserved after,.record source catalogue quota event)
  | .finished .. => none

def State.rank : State prepared → Nat
  | .source cursor => cursor.rank+sourceTail prepared+2
  | .listing _ _ catalogue .. => remainingWeight catalogue catalogue.quotas+3
  | .waiting _ _ catalogue _ _ remaining _ => remainingWeight catalogue remaining+1
  | .working _ _ catalogue _ _ _ rest _ cursor => remainingWeight catalogue rest+cursor.rank+2
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
              simp only [State.rank,SourceQuota.Acquisition.State.rank,sourceTail_domain source generated catalogue result];omega
      | observing =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := SourceQuota.Acquisition.each_actual_step_decreases_source_rank step
            simp only [State.rank];omega
      | validating =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := SourceQuota.Acquisition.each_actual_step_decreases_source_rank step
            simp only [State.rank];omega
      | seeding =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := SourceQuota.Acquisition.each_actual_step_decreases_source_rank step
            simp only [State.rank];omega
      | folding =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := SourceQuota.Acquisition.each_actual_step_decreases_source_rank step
            simp only [State.rank];omega
      | reducing =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := SourceQuota.Acquisition.each_actual_step_decreases_source_rank step
            simp only [State.rank];omega
  | listing source generated catalogue result limit bound =>
      dsimp only [move] at actual;cases Option.some.inj actual
      simp only [State.rank,quotaList_exact];omega
  | waiting source generated catalogue result cached remaining conserved =>
      cases remaining <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,remainingWeight,quotaWeight,List.map_nil,List.map_cons,List.sum_nil,List.sum_cons,RecordAcquisition.initial,RecordAcquisition.State.rank];omega
  | working source generated catalogue result cached quota rest conserved cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,RecordAcquisition.State.rank];omega
      | paying =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := RecordAcquisition.progress step
            simp only [State.rank];omega
      | acquiring =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := RecordAcquisition.progress step
            simp only [State.rank];omega
      | calculating =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := RecordAcquisition.progress step
            simp only [State.rank];omega
      | finishing =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := RecordAcquisition.progress step
            simp only [State.rank];omega
      | body =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := RecordAcquisition.progress step
            simp only [State.rank];omega
      | work =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := RecordAcquisition.progress step
            simp only [State.rank];omega
      | sealing =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := RecordAcquisition.progress step
            simp only [State.rank];omega
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
  | listing => simp [move,State.done]
  | waiting source generated catalogue result cached remaining conserved => cases remaining <;> simp [move,State.done]
  | working source generated catalogue result cached quota rest conserved cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | paying | acquiring | calculating | finishing | body | work | sealing =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (RecordAcquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | finished => simp [move,State.done]
end MenuAcquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid
namespace CandidateAcquisition
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}
private def packRecord (outcome : Outcome prepared units) (generated : outcome = generate prepared units) : Record prepared units := ⟨outcome,generated⟩
private theorem canonical (made : Record prepared units) : made = record prepared units := by
  rcases made with ⟨outcome,generated⟩;cases generated;rfl
private theorem programme_exact (paid : PaidSelection.Funded prepared units) (paid_exact : PaidSelection.pay prepared units = .paid paid)
    (actual : PaidSelection.Available paid.family) (acquired : PaidSelection.acquire paid.family = .ready actual)
    (calculation : Calculation actual.pool units) (generated : calculation = calculate actual.pool units) :
    finish (⟨paid,actual,calculation,generated⟩ : Programme prepared units) = generate prepared units := by
  cases generated
  simp only [generate,paid_exact,acquired]

inductive State (prepared : Prepared input) (units : Nat) where
  | paying (cursor : PaidSelection.PaymentAcquisition.State prepared units)
  | acquiring (paid : PaidSelection.Funded prepared units) (generated : PaidSelection.pay prepared units = .paid paid)
      (cursor : PaidSelection.SourceAcquisition.State paid.family)
  | calculating (paid : PaidSelection.Funded prepared units) (generated : PaidSelection.pay prepared units = .paid paid)
      (actual : PaidSelection.Available paid.family) (acquired : PaidSelection.acquire paid.family = .ready actual)
      (cursor : Counter.Acquisition.State actual.pool units)
  | finishing (made : Programme prepared units) (generated : finish made = generate prepared units)
  | body (made : Programme prepared units) (generated : finish made = generate prepared units)
      (value : Nat) (completed : made.calculation.run.endpoint = .program [value] [])
      (correct : value = Body.units made.actual.pool + Work.workBudget made.actual.pool)
      (result : made.calculation.result = .budget value completed correct)
      (covered : made.calculation.run.spent+value ≤ units)
  | work (made : Programme prepared units) (generated : finish made = generate prepared units)
      (value : Nat) (completed : made.calculation.run.endpoint = .program [value] [])
      (correct : value = Body.units made.actual.pool + Work.workBudget made.actual.pool)
      (result : made.calculation.result = .budget value completed correct)
      (covered : made.calculation.run.spent+value ≤ units)
      (body : Body.Generated made.actual.pool) (body_generated : body = Body.generate made.actual.pool)
  | sealing (outcome : Outcome prepared units) (generated : outcome = generate prepared units)
  | finished (made : Record prepared units) (generated : made = record prepared units)
inductive Event (prepared : Prepared input) (units : Nat) where
  | paymentStep (event : PaidSelection.PaymentAcquisition.Event prepared units)
  | sourceStep (paid : PaidSelection.Funded prepared units) (event : PaidSelection.SourceAcquisition.Event paid.family)
  | payment (attempt : PaidSelection.Attempt prepared units) (actual : attempt = PaidSelection.pay prepared units)
  | source (paid : PaidSelection.Funded prepared units) (view : PaidSelection.View paid.family) (actual : view = PaidSelection.acquire paid.family)
  | counter (paid : PaidSelection.Funded prepared units) (actual : PaidSelection.Available paid.family)
      (event : Counter.Acquisition.Event actual.pool units)
  | counted (made : Programme prepared units)
  | disposition (outcome : Outcome prepared units)
  | body (made : Programme prepared units) (body : Body.Generated made.actual.pool) (generated : body = Body.generate made.actual.pool)
  | selection (made : Programme prepared units) (work : Work.Generated made.actual.pool) (generated : work = Work.generate made.actual.pool)
  | cached (made : Record prepared units) (generated : made = record prepared units)

def initial (prepared : Prepared input) (units : Nat) : State prepared units := .paying (PaidSelection.PaymentAcquisition.initial prepared units)

def move : State prepared units → Option (State prepared units × Event prepared units)
  | .paying (.finished (.failed why) actual) =>
      some (.sealing (.unfunded why) (by simp only [generate,←actual]),.payment (.failed why) actual)
  | .paying (.finished (.paid paid) actual) =>
      some (.acquiring paid actual.symm (PaidSelection.SourceAcquisition.initial paid.family),.payment (.paid paid) actual)
  | .paying cursor@(.opening) | .paying cursor@(.funding ..) | .paying cursor@(.checking ..) =>
      match _step : PaidSelection.PaymentAcquisition.move cursor with
      | none => none
      | some (after,event) => some (.paying after,.paymentStep event)
  | .acquiring paid generated (.finished (.missing source why) acquired) =>
      some (.sealing (.unavailable paid source why) (by simp only [generate,generated,←acquired]),.source paid (.missing source why) acquired)
  | .acquiring paid generated (.finished (.ready actual) acquired) =>
      some (.calculating paid generated actual acquired.symm (Counter.Acquisition.initial actual.pool units),.source paid (.ready actual) acquired)
  | .acquiring paid generated cursor@(.source ..) | .acquiring paid generated cursor@(.pool ..) =>
      match _step : PaidSelection.SourceAcquisition.move cursor with
      | none => none
      | some (after,event) => some (.acquiring paid generated after,.sourceStep paid event)
  | .calculating paid generated actual acquired (.finished calculation calculated) =>
      let made : Programme prepared units := ⟨paid,actual,calculation,calculated⟩
      some (.finishing made (programme_exact paid generated actual acquired calculation calculated),.counted made)
  | .calculating paid generated actual acquired cursor@(.running ..) =>
      match _step : Counter.Acquisition.move actual.pool units cursor with
      | none => none
      | some (after,event) => some (.calculating paid generated actual acquired after,.counter paid actual event)
  | .finishing made generated => match result : made.calculation.result with
    | .exhausted state residual all_spent =>
        let outcome := Outcome.exhausted made state residual all_spent
        some (.sealing outcome (by simpa only [finish,result] using generated),.disposition outcome)
    | .budget value completed correct =>
        if covered : made.calculation.run.spent+value ≤ units then
          some (.body made generated value completed correct result covered,.counted made)
        else
          let outcome := Outcome.shortfall made value completed correct (Nat.lt_of_not_ge covered)
          some (.sealing outcome (by simpa only [finish,result,dif_neg covered] using generated),.disposition outcome)
  | .body made generated value completed correct result covered =>
      let body := Body.generate made.actual.pool
      some (.work made generated value completed correct result covered body rfl,.body made body rfl)
  | .work made generated value completed correct result covered body bodyGenerated =>
      let work := Work.generate made.actual.pool
      let release : Release prepared units := ⟨made,value,completed,correct,covered,body,bodyGenerated,work,rfl⟩
      some (.sealing (.released release) (by
        cases bodyGenerated
        simpa only [finish,result,dif_pos covered] using generated),.selection made work rfl)
  | .sealing outcome generated =>
      let made := packRecord outcome generated
      some (.finished made (canonical made),.cached made (canonical made))
  | .finished .. => none

def afterPay (prepared : Prepared input) (units : Nat) :=
  match PaidSelection.pay prepared units with
  | .paid paid => (PaidSelection.SourceAcquisition.initial paid.family).rank
  | .failed _ => 0
private theorem afterPay_exact (paid : PaidSelection.Funded prepared units) (generated : PaidSelection.pay prepared units = .paid paid) :
    afterPay prepared units = (PaidSelection.SourceAcquisition.initial paid.family).rank := by simp only [afterPay,generated]
def State.rank : State prepared units → Nat
  | .paying cursor => cursor.rank+afterPay prepared units+units+9
  | .acquiring _ _ cursor => cursor.rank+units+8
  | .calculating _ _ _ _ cursor => cursor.rank _ units+6
  | .finishing .. => 5
  | .body .. => 4
  | .work .. => 3
  | .sealing .. => 1
  | .finished .. => 0
def State.done : State prepared units → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared units} {event : Event prepared units}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | paying cursor =>
      cases cursor with
      | finished attempt generated =>
          cases attempt with
          | failed => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,PaidSelection.PaymentAcquisition.State.rank];omega
          | paid paid =>
              dsimp only [move] at actual;cases Option.some.inj actual
              simp only [State.rank,PaidSelection.PaymentAcquisition.State.rank,afterPay_exact paid generated.symm];omega
      | opening | funding | checking =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := PaidSelection.PaymentAcquisition.progress step;simp only [State.rank];omega)
  | acquiring paid generated cursor =>
      cases cursor with
      | finished view acquired =>
          cases view <;> dsimp only [move] at actual <;> cases Option.some.inj actual
          all_goals simp only [State.rank,PaidSelection.SourceAcquisition.State.rank,Counter.Acquisition.initial,Counter.Acquisition.State.rank];omega
      | source | pool =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := PaidSelection.SourceAcquisition.progress step;simp only [State.rank];omega)
  | calculating paid generated acquired sourceEq cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Counter.Acquisition.State.rank];omega
      | running =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step;cases Option.some.inj actual
            have less := Counter.Acquisition.progress acquired.pool units step
            simp only [State.rank];omega
  | finishing =>
      dsimp only [move] at actual;split at actual
      · cases Option.some.inj actual;simp only [State.rank];omega
      · split at actual
        all_goals cases Option.some.inj actual;simp only [State.rank];omega
  | body | work | sealing =>
      all_goals dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual

theorem no_move_iff_done (before : State prepared units) : move before = none ↔ before.done = true := by
  cases before with
  | paying cursor =>
      cases cursor with
      | finished attempt => cases attempt <;> simp [move,State.done]
      | opening | funding | checking =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (PaidSelection.PaymentAcquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | acquiring paid generated cursor =>
      cases cursor with
      | finished view => cases view <;> simp [move,State.done]
      | source | pool =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (PaidSelection.SourceAcquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | calculating paid generated actual acquired cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | running =>
          dsimp only [move,State.done];split
          · rename_i stopped;have done := (Counter.Acquisition.no_move_iff_done actual.pool units _).mp stopped;cases done
          · simp
  | finishing => dsimp only [move,State.done];split <;> first | (split <;> simp) | simp
  | body | work | sealing | finished => simp [move,State.done]
end CandidateAcquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid
namespace CandidateMenu
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}
  {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
abbrev Entry (catalogue : SourceQuota.Catalogue source.snapshot) := Sigma fun quota : catalogue.Quota => Record prepared quota.val
private def quotaList (catalogue : SourceQuota.Catalogue source.snapshot) (limit : Nat) (bound : limit = catalogue.bound) : List catalogue.Quota :=
  (List.finRange (limit+1)).map fun quota => ⟨quota.val,by rw [←bound];exact quota.isLt⟩
private theorem quotaList_exact (catalogue : SourceQuota.Catalogue source.snapshot) (limit : Nat) (bound : limit = catalogue.bound) :
    quotaList catalogue limit bound = catalogue.quotas := by
  subst limit
  simp only [quotaList,SourceQuota.Catalogue.quotas]
  exact List.map_id _
private theorem candidates_canonical (made : Candidates source catalogue) : made = candidates source catalogue := by
  rcases made with ⟨entries,generated⟩;cases generated;rfl
private def packCandidates (cached : List (Entry catalogue))
    (generated : cached = catalogue.quotas.map (fun quota => ⟨quota,record prepared quota.val⟩)) : Candidates source catalogue := ⟨cached,generated⟩
private theorem empty_exact (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
    (absent : source.snapshot.cached = []) (result : source.result = .empty absent) :
    DomainResult.empty source absent = generateAll prepared := by
  cases generated
  dsimp only [generateAll]
  split
  · rfl
  · rename_i cell listed broken observed;cases result.symm.trans observed
  · rename_i catalogue observed;cases result.symm.trans observed
private theorem blocked_exact (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
    (cell : SourceQuota.CachedCell prepared) (listed : cell ∈ source.snapshot.cached) (broken : cell.2.units.isSome = false)
    (result : source.result = .blocked cell listed broken) :
    DomainResult.blocked source cell listed broken = generateAll prepared := by
  cases generated
  dsimp only [generateAll]
  split
  · rename_i absent observed;cases result.symm.trans observed
  · rename_i other inside failure observed
    cases SourceQuota.Result.blocked.inj (result.symm.trans observed)
    rfl
  · rename_i catalogue observed;cases result.symm.trans observed
private theorem ready_exact (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
    (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue)
    (made : Candidates source catalogue) (actual : made = candidates source catalogue) :
    DomainResult.ready source catalogue result made = generateAll prepared := by
  cases generated;cases actual
  dsimp only [generateAll]
  split
  · rename_i absent observed;cases result.symm.trans observed
  · rename_i cell listed broken observed;cases result.symm.trans observed
  · rename_i other observed
    cases SourceQuota.Result.domain.inj (result.symm.trans observed)
    rfl

def quotaWeight (quota : catalogue.Quota) := (CandidateAcquisition.initial prepared quota.val).rank+3
def remainingWeight (catalogue : SourceQuota.Catalogue source.snapshot) (remaining : List catalogue.Quota) := (remaining.map quotaWeight).sum
def sourceTail (prepared : Prepared input) :=
  let source := SourceQuota.generate prepared
  match source.result with
  | .domain catalogue => remainingWeight catalogue catalogue.quotas+4
  | _ => 0
private theorem sourceTail_domain (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
    (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue) :
    sourceTail prepared = remainingWeight catalogue catalogue.quotas+4 := by
  cases generated
  dsimp only [sourceTail]
  rw [result]

inductive State (prepared : Prepared input) where
  | source (cursor : SourceQuota.Acquisition.State prepared)
  | listing (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue) (limit : Nat) (bound : limit = catalogue.bound)
  | waiting (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue)
      (cached : List (Entry catalogue)) (remaining : List catalogue.Quota)
      (conserved : cached++remaining.map (fun quota => ⟨quota,record prepared quota.val⟩) = catalogue.quotas.map (fun quota => ⟨quota,record prepared quota.val⟩))
  | working (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
      (catalogue : SourceQuota.Catalogue source.snapshot) (result : source.result = .domain catalogue)
      (cached : List (Entry catalogue)) (quota : catalogue.Quota) (rest : List catalogue.Quota)
      (conserved : cached++(quota::rest).map (fun quota => ⟨quota,record prepared quota.val⟩) = catalogue.quotas.map (fun quota => ⟨quota,record prepared quota.val⟩))
      (cursor : CandidateAcquisition.State prepared quota.val)
  | finished (menu : DomainResult prepared) (generated : menu = generateAll prepared)
def initial (prepared : Prepared input) : State prepared := .source (SourceQuota.Acquisition.initial prepared)
inductive Event (prepared : Prepared input) where
  | source (event : SourceQuota.Acquisition.Event prepared)
  | captured (source : SourceQuota.Generated prepared) (generated : source = SourceQuota.generate prepared)
  | enumerated (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot) (limit : Nat) (bound : limit = catalogue.bound)
  | opened (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot) (quota : catalogue.Quota)
  | record (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot) (quota : catalogue.Quota)
      (event : CandidateAcquisition.Event prepared quota.val)
  | cached (source : SourceQuota.Generated prepared) (catalogue : SourceQuota.Catalogue source.snapshot) (quota : catalogue.Quota)
      (made : Record prepared quota.val) (generated : made = Paid.record prepared quota.val)
  | complete (menu : DomainResult prepared) (generated : menu = generateAll prepared)

def move : State prepared → Option (State prepared × Event prepared)
  | .source (.finished (.unavailable source generated outside)) => match result : source.result with
    | .empty absent => some (.finished (.empty source absent) (empty_exact source generated absent result),.captured source generated)
    | .blocked cell listed broken => some (.finished (.blocked source cell listed broken) (blocked_exact source generated cell listed broken result),.captured source generated)
    | .domain catalogue => False.elim (by rw [result] at outside;exact outside)
  | .source (.finished (.domain source generated catalogue result limit bound)) =>
      some (.listing source generated catalogue result limit bound,.captured source generated)
  | .source cursor@(.observing ..) | .source cursor@(.validating ..) | .source cursor@(.seeding ..)
  | .source cursor@(.folding ..) | .source cursor@(.reducing ..) => match _actual : SourceQuota.Acquisition.move cursor with
    | none => none
    | some (after,event) => some (.source after,.source event)
  | .listing source generated catalogue result limit bound =>
      some (.waiting source generated catalogue result [] (quotaList catalogue limit bound) (by
        rw [quotaList_exact];rfl),.enumerated source catalogue limit bound)
  | .waiting source generated catalogue result cached [] conserved =>
      let made := packCandidates cached (by simpa only [List.map_nil,List.append_nil] using conserved)
      let menu := DomainResult.ready source catalogue result made
      let exact := ready_exact source generated catalogue result made (candidates_canonical made)
      some (.finished menu exact,.complete menu exact)
  | .waiting source generated catalogue result cached (quota::rest) conserved =>
      some (.working source generated catalogue result cached quota rest conserved (CandidateAcquisition.initial prepared quota.val),.opened source catalogue quota)
  | .working source generated catalogue result cached quota rest conserved (.finished made actual) =>
      some (.waiting source generated catalogue result (cached++[⟨quota,made⟩]) rest (by
        simpa only [actual,List.map_cons,List.append_assoc,List.singleton_append] using conserved),.cached source catalogue quota made actual)
  | .working source generated catalogue result cached quota rest conserved cursor@(.paying ..)
  | .working source generated catalogue result cached quota rest conserved cursor@(.acquiring ..)
  | .working source generated catalogue result cached quota rest conserved cursor@(.calculating ..)
  | .working source generated catalogue result cached quota rest conserved cursor@(.finishing ..)
  | .working source generated catalogue result cached quota rest conserved cursor@(.body ..)
  | .working source generated catalogue result cached quota rest conserved cursor@(.work ..)
  | .working source generated catalogue result cached quota rest conserved cursor@(.sealing ..) =>
      match _actual : CandidateAcquisition.move cursor with
      | none => none
      | some (after,event) => some (.working source generated catalogue result cached quota rest conserved after,.record source catalogue quota event)
  | .finished .. => none

def State.rank : State prepared → Nat
  | .source cursor => cursor.rank+sourceTail prepared+2
  | .listing _ _ catalogue .. => remainingWeight catalogue catalogue.quotas+3
  | .waiting _ _ catalogue _ _ remaining _ => remainingWeight catalogue remaining+1
  | .working _ _ catalogue _ _ _ rest _ cursor => remainingWeight catalogue rest+cursor.rank+2
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
              simp only [State.rank,SourceQuota.Acquisition.State.rank,sourceTail_domain source generated catalogue result];omega
      | observing =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := SourceQuota.Acquisition.each_actual_step_decreases_source_rank step
            simp only [State.rank];omega
      | validating =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := SourceQuota.Acquisition.each_actual_step_decreases_source_rank step
            simp only [State.rank];omega
      | seeding =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := SourceQuota.Acquisition.each_actual_step_decreases_source_rank step
            simp only [State.rank];omega
      | folding =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := SourceQuota.Acquisition.each_actual_step_decreases_source_rank step
            simp only [State.rank];omega
      | reducing =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := SourceQuota.Acquisition.each_actual_step_decreases_source_rank step
            simp only [State.rank];omega
  | listing source generated catalogue result limit bound =>
      dsimp only [move] at actual;cases Option.some.inj actual
      simp only [State.rank,quotaList_exact];omega
  | waiting source generated catalogue result cached remaining conserved =>
      cases remaining <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,remainingWeight,quotaWeight,List.map_nil,List.map_cons,List.sum_nil,List.sum_cons,CandidateAcquisition.initial,CandidateAcquisition.State.rank];omega
  | working source generated catalogue result cached quota rest conserved cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,CandidateAcquisition.State.rank];omega
      | paying =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := CandidateAcquisition.progress step
            simp only [State.rank];omega
      | acquiring =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := CandidateAcquisition.progress step
            simp only [State.rank];omega
      | calculating =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := CandidateAcquisition.progress step
            simp only [State.rank];omega
      | finishing =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := CandidateAcquisition.progress step
            simp only [State.rank];omega
      | body =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := CandidateAcquisition.progress step
            simp only [State.rank];omega
      | work =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := CandidateAcquisition.progress step
            simp only [State.rank];omega
      | sealing =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := CandidateAcquisition.progress step
            simp only [State.rank];omega
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
  | listing => simp [move,State.done]
  | waiting source generated catalogue result cached remaining conserved => cases remaining <;> simp [move,State.done]
  | working source generated catalogue result cached quota rest conserved cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | paying | acquiring | calculating | finishing | body | work | sealing =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (CandidateAcquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | finished => simp [move,State.done]
end CandidateMenu
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid
